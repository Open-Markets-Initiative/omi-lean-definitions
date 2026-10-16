import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) TotalView Itch v3.1.f

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesTotalviewAsciiitchV31FClient

/-- Debug Packet -/
structure DebugPacket where
  text : List UInt8
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  encodeMany Byte.encode message.text

def decode (bytes : List UInt8) : Option DebugPacket := do
  let text ← decodeAll Byte.decode bytes.length bytes
  pure { text }

theorem decode_encode (message : DebugPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.text _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.text), some_bind]
  rfl

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
  unsequencedMessage : List UInt8
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeMany Byte.encode message.unsequencedMessage

def decode (bytes : List UInt8) : Option UnsequencedDataPacket := do
  let unsequencedMessage ← decodeAll Byte.decode bytes.length bytes
  pure { unsequencedMessage }

theorem decode_encode (message : UnsequencedDataPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.unsequencedMessage _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.unsequencedMessage), some_bind]
  rfl

end UnsequencedDataPacket

/-- Any Client Payload, selected by Client Packet Type -/
inductive ClientPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- "L" 0x4C
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Client Packet Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginRequestPacket _ => 76
  | .unsequencedDataPacket _ => 85

def encode : ClientPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginRequestPacket message => LoginRequestPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ClientPayload :=
  if tag = 43 then (DebugPacket.decode bytes).map fun message => .debugPacket message
  else if tag = 76 then (LoginRequestPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequestPacket message) else none
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).map fun message => .unsequencedDataPacket message
  else none

theorem decode_encode (message : ClientPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode]
  | loginRequestPacket message => simp [decode, encode, tag, LoginRequestPacket.decode_encode_nil]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode]

end ClientPayload

/-- Client Frame -/
structure ClientFrameBody where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientFrameBody

def encodeBody (message : ClientFrameBody) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option ClientFrameBody := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let clientPayload ← ClientPayload.decode clientPacketType bytes
  pure { clientPayload }

theorem decodeBody_encodeBody (message : ClientFrameBody) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

end ClientFrameBody

/-- Client Frame: the body, which the record carries with the proof it holds no soupLf -/
abbrev ClientFrame := Closed ClientFrameBody.encodeBody 10

namespace ClientFrame

def encode (message : ClientFrame) : List UInt8 :=
  encodeClosed 10 ClientFrameBody.encodeBody message.val

def decode : List UInt8 → Option (ClientFrame × List UInt8) :=
  decodeClosing 10 ClientFrameBody.encodeBody ClientFrameBody.decodeBody

@[simp] theorem decode_encode (message : ClientFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeClosing_encodeClosed 10 ClientFrameBody.encodeBody ClientFrameBody.decodeBody message (ClientFrameBody.decodeBody_encodeBody message.val) rest

/-- Every encoding is at least the byte that closes it -/
theorem encode_length_pos (message : ClientFrame) : (encode message).length > 0 := by
  unfold encode
  exact encodeClosed_length_pos 10 ClientFrameBody.encodeBody message.val

end ClientFrame

/-- Client Packet -/
structure ClientPacket where
  clientFrame : List ClientFrame
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientFrame.encode message.clientFrame

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientFrame ← decodeAll ClientFrame.decode bytes.length bytes
  pure { clientFrame }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientFrame.encode ClientFrame.decode ClientFrame.decode_encode ClientFrame.encode_length_pos message.clientFrame _ (encodeMany_length_ge ClientFrame.encode ClientFrame.encode_length_pos message.clientFrame), some_bind]
  rfl

end ClientPacket

end Omi.NasdaqNsmequitiesTotalviewAsciiitchV31FClient
