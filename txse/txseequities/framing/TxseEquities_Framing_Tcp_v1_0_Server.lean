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

namespace Omi.TxseTxseequitiesFramingTcpV10Server

/-- Debug Message -/
structure DebugMessage where
  text : Capped 65504
  deriving DecidableEq, Repr

namespace DebugMessage

def encode (message : DebugMessage) : List UInt8 :=
  message.text.val

def decode (bytes : List UInt8) : Option DebugMessage := do
  let text_ := bytes
  if fits_text : text_.length ≤ 65504 then
    pure { text := ⟨text_, fits_text⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DebugMessage) : (encode message).length ≤ 65504 := by
  have bound_text := message.text.length_le
  unfold encode
  omega

theorem decode_encode (message : DebugMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.text.length_le]
  rfl

end DebugMessage

/-- End Of Session Message: 0 bytes -/
structure EndOfSessionMessage where
  deriving DecidableEq, Repr

namespace EndOfSessionMessage

def encode (_ : EndOfSessionMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSessionMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSessionMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSessionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfSessionMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EndOfSessionMessage

/-- Logon Response Message: 30 bytes -/
structure LogonResponseMessage where
  session : BitVec 64
  nextSequenceNumber : BitVec 64
  highestKnownSequenceNumber : BitVec 64
  logonResponseCode : BitVec 8
  numberStreamIds : BitVec 8
  instance_ : BitVec 32
  deriving DecidableEq, Repr

namespace LogonResponseMessage

def encode (message : LogonResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.session
    ++ (encodeUIntLE 8 message.nextSequenceNumber
    ++ (encodeUIntLE 8 message.highestKnownSequenceNumber
    ++ (encodeUInt 1 message.logonResponseCode
    ++ (encodeUInt 1 message.numberStreamIds
    ++ (encodeUIntLE 4 message.instance_)))))

def decode (bytes : List UInt8) : Option (LogonResponseMessage × List UInt8) := do
  let (session, bytes) ← decodeUIntLE 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (highestKnownSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (logonResponseCode, bytes) ← decodeUInt 1 bytes
  let (numberStreamIds, bytes) ← decodeUInt 1 bytes
  let (instance_, bytes) ← decodeUIntLE 4 bytes
  pure ({ session, nextSequenceNumber, highestKnownSequenceNumber, logonResponseCode, numberStreamIds, instance_ }, bytes)

@[simp] theorem encode_length (message : LogonResponseMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LogonResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogonResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LogonResponseMessage

/-- Tcp Sequenced Message -/
structure TcpSequencedMessage where
  streamId : BitVec 8
  messageType : BitVec 8
  sequencedMessage : Capped 65504
  deriving DecidableEq, Repr

namespace TcpSequencedMessage

def encode (message : TcpSequencedMessage) : List UInt8 :=
  encodeUInt 1 message.streamId
    ++ (encodeUInt 1 message.messageType
    ++ (message.sequencedMessage.val))

def decode (bytes : List UInt8) : Option TcpSequencedMessage := do
  let (streamId, bytes) ← decodeUInt 1 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let sequencedMessage_ := bytes
  if fits_sequencedMessage : sequencedMessage_.length ≤ 65504 then
    pure { streamId, messageType, sequencedMessage := ⟨sequencedMessage_, fits_sequencedMessage⟩ }
  else none

theorem encode_length_pos (message : TcpSequencedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TcpSequencedMessage) : (encode message).length ≤ 65506 := by
  have bound_sequencedMessage := message.sequencedMessage.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length]
  omega

theorem decode_encode (message : TcpSequencedMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.sequencedMessage.length_le]
  rfl

end TcpSequencedMessage

/-- Any Server Payload, selected by Packet Type -/
inductive ServerPayload where
  | debugMessage (message : DebugMessage) -- 48
  | endOfSessionMessage (message : EndOfSessionMessage) -- 52
  | logonResponseMessage (message : LogonResponseMessage) -- 49
  | tcpSequencedMessage (message : TcpSequencedMessage) -- 50
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugMessage _ => 48
  | .endOfSessionMessage _ => 52
  | .logonResponseMessage _ => 49
  | .tcpSequencedMessage _ => 50

def encode : ServerPayload → List UInt8
  | .debugMessage message => DebugMessage.encode message
  | .endOfSessionMessage message => EndOfSessionMessage.encode message
  | .logonResponseMessage message => LogonResponseMessage.encode message
  | .tcpSequencedMessage message => TcpSequencedMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 65506 := by
  cases message with
  | debugMessage inner =>
    have bound_inner := DebugMessage.encode_length_le inner
    simp only [encode]
    omega
  | endOfSessionMessage inner =>
    simp only [encode, EndOfSessionMessage.encode_length]
    omega
  | logonResponseMessage inner =>
    simp only [encode, LogonResponseMessage.encode_length]
    omega
  | tcpSequencedMessage inner =>
    have bound_inner := TcpSequencedMessage.encode_length_le inner
    simp only [encode]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ServerPayload :=
  if tag = 48 then (DebugMessage.decode bytes).map fun message => .debugMessage message
  else if tag = 52 then (EndOfSessionMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfSessionMessage message) else none
  else if tag = 49 then (LogonResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logonResponseMessage message) else none
  else if tag = 50 then (TcpSequencedMessage.decode bytes).map fun message => .tcpSequencedMessage message
  else none

theorem decode_encode (message : ServerPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugMessage message => simp [decode, encode, tag, DebugMessage.decode_encode]
  | endOfSessionMessage message => simp [decode, encode, tag, EndOfSessionMessage.decode_encode_nil]
  | logonResponseMessage message => simp [decode, encode, tag, LogonResponseMessage.decode_encode_nil]
  | tcpSequencedMessage message => simp [decode, encode, tag, TcpSequencedMessage.decode_encode]

end ServerPayload

/-- Server Rake Tcp Message -/
structure ServerRakeTcpMessage where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerRakeTcpMessage

def encodeBody (message : ServerRakeTcpMessage) : List UInt8 :=
  encodeUIntLE 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option ServerRakeTcpMessage := do
  let (packetType, bytes) ← decodeUIntLE 1 bytes
  let serverPayload ← ServerPayload.decode packetType bytes
  pure { serverPayload }

theorem decodeBody_encodeBody (message : ServerRakeTcpMessage) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerRakeTcpMessage) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverPayload with
  | debugMessage inner =>
    have bound_inner := DebugMessage.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | endOfSessionMessage inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, EndOfSessionMessage.encode_length]
    omega
  | logonResponseMessage inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, LogonResponseMessage.encode_length]
    omega
  | tcpSequencedMessage inner =>
    have bound_inner := TcpSequencedMessage.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ServerRakeTcpMessage → List UInt8 :=
  encodeFramedLE 2 0 encodeBody

def decode : List UInt8 → Option (ServerRakeTcpMessage × List UInt8) :=
  decodeFramedAllLE 2 0 decodeBody

@[simp] theorem decode_encode (message : ServerRakeTcpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerRakeTcpMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end ServerRakeTcpMessage

/-- Server Packet -/
structure ServerPacket where
  serverRakeTcpMessage : List ServerRakeTcpMessage
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerRakeTcpMessage.encode message.serverRakeTcpMessage

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverRakeTcpMessage ← decodeAll ServerRakeTcpMessage.decode bytes.length bytes
  pure { serverRakeTcpMessage }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerRakeTcpMessage.encode ServerRakeTcpMessage.decode ServerRakeTcpMessage.decode_encode ServerRakeTcpMessage.encode_length_pos message.serverRakeTcpMessage _ (encodeMany_length_ge ServerRakeTcpMessage.encode ServerRakeTcpMessage.encode_length_pos message.serverRakeTcpMessage), some_bind]
  rfl

end ServerPacket

end Omi.TxseTxseequitiesFramingTcpV10Server
