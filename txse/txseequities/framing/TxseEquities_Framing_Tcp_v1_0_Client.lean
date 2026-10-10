import Wire

/-!
# Texas Stock Exchange  v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TxseTxseequitiesFramingTcpV10Client

/-- Logon Request Packet: 32 bytes -/
structure LogonRequestPacket where
  session : BitVec 64
  senderComp : Alpha 8
  token : Alpha 8
  nextSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LogonRequestPacket

def encode (message : LogonRequestPacket) : List UInt8 :=
  encodeUIntLE 8 message.session
    ++ (Alpha.encode message.senderComp
    ++ (Alpha.encode message.token
    ++ (encodeUIntLE 8 message.nextSequenceNumber)))

def decode (bytes : List UInt8) : Option (LogonRequestPacket × List UInt8) := do
  let (session, bytes) ← decodeUIntLE 8 bytes
  let (senderComp, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← Alpha.decode 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ session, senderComp, token, nextSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LogonRequestPacket) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : LogonRequestPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonRequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogonRequestPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LogonRequestPacket

/-- Tcp Unsequenced Message -/
structure TcpUnsequencedMessage where
  messageType : BitVec 8
  unsequencedMessage : Capped 65502
  deriving DecidableEq, Repr

namespace TcpUnsequencedMessage

def encode (message : TcpUnsequencedMessage) : List UInt8 :=
  encodeUInt 1 message.messageType
    ++ (message.unsequencedMessage.val)

def decode (bytes : List UInt8) : Option TcpUnsequencedMessage := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let unsequencedMessage_ := bytes
  if fits_unsequencedMessage : unsequencedMessage_.length ≤ 65502 then
    pure { messageType, unsequencedMessage := ⟨unsequencedMessage_, fits_unsequencedMessage⟩ }
  else none

theorem encode_length_pos (message : TcpUnsequencedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TcpUnsequencedMessage) : (encode message).length ≤ 65503 := by
  have bound_unsequencedMessage := message.unsequencedMessage.length_le
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

theorem decode_encode (message : TcpUnsequencedMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.unsequencedMessage.length_le]
  rfl

end TcpUnsequencedMessage

/-- Any Client Payload, selected by Packet Type -/
inductive ClientPayload where
  | logonRequestPacket (message : LogonRequestPacket) -- 53
  | tcpUnsequencedMessage (message : TcpUnsequencedMessage) -- 54
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Packet Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .logonRequestPacket _ => 53
  | .tcpUnsequencedMessage _ => 54

def encode : ClientPayload → List UInt8
  | .logonRequestPacket message => LogonRequestPacket.encode message
  | .tcpUnsequencedMessage message => TcpUnsequencedMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 65503 := by
  cases message with
  | logonRequestPacket inner =>
    simp only [encode, LogonRequestPacket.encode_length]
    omega
  | tcpUnsequencedMessage inner =>
    have bound_inner := TcpUnsequencedMessage.encode_length_le inner
    simp only [encode]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ClientPayload :=
  if tag = 53 then (LogonRequestPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logonRequestPacket message) else none
  else if tag = 54 then (TcpUnsequencedMessage.decode bytes).map fun message => .tcpUnsequencedMessage message
  else none

theorem decode_encode (message : ClientPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | logonRequestPacket message => simp [decode, encode, tag, LogonRequestPacket.decode_encode_nil]
  | tcpUnsequencedMessage message => simp [decode, encode, tag, TcpUnsequencedMessage.decode_encode]

end ClientPayload

/-- Client Rake Tcp Message -/
structure ClientRakeTcpMessage where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientRakeTcpMessage

def encodeBody (message : ClientRakeTcpMessage) : List UInt8 :=
  encodeUIntLE 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option ClientRakeTcpMessage := do
  let (packetType, bytes) ← decodeUIntLE 1 bytes
  let clientPayload ← ClientPayload.decode packetType bytes
  pure { clientPayload }

theorem decodeBody_encodeBody (message : ClientRakeTcpMessage) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientRakeTcpMessage) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.clientPayload with
  | logonRequestPacket inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, LogonRequestPacket.encode_length]
    omega
  | tcpUnsequencedMessage inner =>
    have bound_inner := TcpUnsequencedMessage.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ClientRakeTcpMessage → List UInt8 :=
  encodeFramedLE 2 0 encodeBody

def decode : List UInt8 → Option (ClientRakeTcpMessage × List UInt8) :=
  decodeFramedAllLE 2 0 decodeBody

@[simp] theorem decode_encode (message : ClientRakeTcpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ClientRakeTcpMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end ClientRakeTcpMessage

/-- Client Packet -/
structure ClientPacket where
  clientRakeTcpMessage : List ClientRakeTcpMessage
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientRakeTcpMessage.encode message.clientRakeTcpMessage

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientRakeTcpMessage ← decodeAll ClientRakeTcpMessage.decode bytes.length bytes
  pure { clientRakeTcpMessage }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientRakeTcpMessage.encode ClientRakeTcpMessage.decode ClientRakeTcpMessage.decode_encode ClientRakeTcpMessage.encode_length_pos message.clientRakeTcpMessage _ (encodeMany_length_ge ClientRakeTcpMessage.encode ClientRakeTcpMessage.encode_length_pos message.clientRakeTcpMessage), some_bind]
  rfl

end ClientPacket

end Omi.TxseTxseequitiesFramingTcpV10Client
