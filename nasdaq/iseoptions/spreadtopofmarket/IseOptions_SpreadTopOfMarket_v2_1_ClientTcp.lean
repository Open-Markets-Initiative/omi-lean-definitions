import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Phlx Options Spread Top Of Market v2.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Unsequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqIseoptionsSpreadtopofmarketItchV21ClientTcp

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  text : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (text, bytes) ← Alpha.decode 1 bytes
  pure ({ text }, bytes)

@[simp] theorem encode_length (message : DebugPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DebugPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebugPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DebugPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DebugPacket

/-- Login Request Packet: 46 bytes -/
structure LoginRequestPacket where
  username : Alpha 6
  password : Alpha 10
  requestedSession : Alpha 10
  requestedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginRequestPacket

def encode (message : LoginRequestPacket) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.requestedSession
    ++ (Alpha.encode message.requestedSequenceNumber)))

def decode (bytes : List UInt8) : Option (LoginRequestPacket × List UInt8) := do
  let (username, bytes) ← Alpha.decode 6 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  let (requestedSession, bytes) ← Alpha.decode 10 bytes
  let (requestedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ username, password, requestedSession, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequestPacket) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequestPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRequestPacket

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessageType : Alpha 1
  unsequencedMessage : Capped 65488
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  Alpha.encode message.unsequencedMessageType
    ++ (message.unsequencedMessage.val)

def decode (bytes : List UInt8) : Option UnsequencedDataPacket := do
  let (unsequencedMessageType, bytes) ← Alpha.decode 1 bytes
  let unsequencedMessage_ := bytes
  if fits_unsequencedMessage : unsequencedMessage_.length ≤ 65488 then
    pure { unsequencedMessageType, unsequencedMessage := ⟨unsequencedMessage_, fits_unsequencedMessage⟩ }
  else none

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 65489 := by
  have bound_unsequencedMessage := message.unsequencedMessage.length_le
  unfold encode
  simp only [List.length_append, Alpha.encode_length]
  omega

theorem decode_encode (message : UnsequencedDataPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.unsequencedMessage.length_le]
  rfl

end UnsequencedDataPacket

/-- Client Heartbeat Packet: 0 bytes -/
structure ClientHeartbeatPacket where
  deriving DecidableEq, Repr

namespace ClientHeartbeatPacket

def encode (_ : ClientHeartbeatPacket) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeatPacket × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeatPacket) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeatPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClientHeartbeatPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ClientHeartbeatPacket

/-- Logout Request Packet: 0 bytes -/
structure LogoutRequestPacket where
  deriving DecidableEq, Repr

namespace LogoutRequestPacket

def encode (_ : LogoutRequestPacket) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutRequestPacket × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutRequestPacket) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutRequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogoutRequestPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LogoutRequestPacket

/-- Any Client Tcp Payload, selected by Client Packet Type -/
inductive ClientTcpPayload where
  | debugPacket (message : DebugPacket) -- '+' 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- 'L' 0x4C
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- 'U' 0x55
  | clientHeartbeatPacket (message : ClientHeartbeatPacket) -- 'R' 0x52
  | logoutRequestPacket (message : LogoutRequestPacket) -- 'O' 0x4F
  deriving DecidableEq, Repr

namespace ClientTcpPayload

/-- The Client Packet Type each message is sent under -/
def tag : ClientTcpPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginRequestPacket _ => 76
  | .unsequencedDataPacket _ => 85
  | .clientHeartbeatPacket _ => 82
  | .logoutRequestPacket _ => 79

def encode : ClientTcpPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginRequestPacket message => LoginRequestPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .clientHeartbeatPacket message => ClientHeartbeatPacket.encode message
  | .logoutRequestPacket message => LogoutRequestPacket.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientTcpPayload) : (encode message).length ≤ 65489 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [encode, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | clientHeartbeatPacket inner =>
    simp only [encode, ClientHeartbeatPacket.encode_length]
    omega
  | logoutRequestPacket inner =>
    simp only [encode, LogoutRequestPacket.encode_length]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ClientTcpPayload :=
  if tag = 43 then (DebugPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.debugPacket message) else none
  else if tag = 76 then (LoginRequestPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequestPacket message) else none
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).map fun message => .unsequencedDataPacket message
  else if tag = 82 then (ClientHeartbeatPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clientHeartbeatPacket message) else none
  else if tag = 79 then (LogoutRequestPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logoutRequestPacket message) else none
  else none

theorem decode_encode (message : ClientTcpPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode_nil]
  | loginRequestPacket message => simp [decode, encode, tag, LoginRequestPacket.decode_encode_nil]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode]
  | clientHeartbeatPacket message => simp [decode, encode, tag, ClientHeartbeatPacket.decode_encode_nil]
  | logoutRequestPacket message => simp [decode, encode, tag, LogoutRequestPacket.decode_encode_nil]

end ClientTcpPayload

/-- Client Soup Bin Tcp Packet -/
structure ClientSoupBinTcpPacket where
  clientTcpPayload : ClientTcpPayload
  deriving DecidableEq, Repr

namespace ClientSoupBinTcpPacket

def encodeBody (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ClientTcpPayload.tag message.clientTcpPayload)
    ++ (ClientTcpPayload.encode message.clientTcpPayload)

def decodeBody (bytes : List UInt8) : Option ClientSoupBinTcpPacket := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let clientTcpPayload ← ClientTcpPayload.decode clientPacketType bytes
  pure { clientTcpPayload }

theorem decodeBody_encodeBody (message : ClientSoupBinTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientTcpPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.clientTcpPayload with
  | debugPacket inner =>
    simp only [ClientTcpPayload.encode, List.length_append, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [ClientTcpPayload.encode, List.length_append, encodeUInt_length, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [ClientTcpPayload.encode, List.length_append, encodeUInt_length]
    omega
  | clientHeartbeatPacket inner =>
    simp only [ClientTcpPayload.encode, List.length_append, encodeUInt_length, ClientHeartbeatPacket.encode_length]
    omega
  | logoutRequestPacket inner =>
    simp only [ClientTcpPayload.encode, List.length_append, encodeUInt_length, LogoutRequestPacket.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ClientSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ClientSoupBinTcpPacket × List UInt8) :=
  decodeFramedAll 2 0 decodeBody

@[simp] theorem decode_encode (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAll_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ClientSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ClientSoupBinTcpPacket

/-- Client Tcp Packet -/
structure ClientTcpPacket where
  clientSoupBinTcpPacket : List ClientSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ClientTcpPacket

def encode (message : ClientTcpPacket) : List UInt8 :=
  encodeMany ClientSoupBinTcpPacket.encode message.clientSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ClientTcpPacket := do
  let clientSoupBinTcpPacket ← decodeAll ClientSoupBinTcpPacket.decode bytes.length bytes
  pure { clientSoupBinTcpPacket }

theorem decode_encode (message : ClientTcpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.decode ClientSoupBinTcpPacket.decode_encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket _ (encodeMany_length_ge ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket), some_bind]
  rfl

end ClientTcpPacket

end Omi.NasdaqIseoptionsSpreadtopofmarketItchV21ClientTcp
