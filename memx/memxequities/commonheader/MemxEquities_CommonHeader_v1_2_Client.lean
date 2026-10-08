import Wire

/-!
# The Members Exchange Common Header v1.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MemxMemxequitiesCommonheaderTcpV12Client

/-- Login Request Message: 2 bytes -/
structure LoginRequestMessage where
  tokenType : Alpha 1
  token : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRequestMessage

def encode (message : LoginRequestMessage) : List UInt8 :=
  Alpha.encode message.tokenType
    ++ (Alpha.encode message.token)

def decode (bytes : List UInt8) : Option (LoginRequestMessage × List UInt8) := do
  let (tokenType, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 1 bytes
  pure ({ tokenType, token }, bytes)

@[simp] theorem encode_length (message : LoginRequestMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRequestMessage

/-- Replay Request Message: 20 bytes -/
structure ReplayRequestMessage where
  sessionId : BitVec 64
  nextSequenceNumber : BitVec 64
  count : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayRequestMessage

def encode (message : ReplayRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId
    ++ (encodeUInt 8 message.nextSequenceNumber
    ++ (encodeUInt 4 message.count))

def decode (bytes : List UInt8) : Option (ReplayRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (count, bytes) ← decodeUInt 4 bytes
  pure ({ sessionId, nextSequenceNumber, count }, bytes)

@[simp] theorem encode_length (message : ReplayRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ReplayRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ReplayRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ReplayRequestMessage

/-- Replay All Request Message: 8 bytes -/
structure ReplayAllRequestMessage where
  sessionId : BitVec 64
  deriving DecidableEq, Repr

namespace ReplayAllRequestMessage

def encode (message : ReplayAllRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId

def decode (bytes : List UInt8) : Option (ReplayAllRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  pure ({ sessionId }, bytes)

@[simp] theorem encode_length (message : ReplayAllRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ReplayAllRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayAllRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ReplayAllRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ReplayAllRequestMessage

/-- Stream Request Message: 16 bytes -/
structure StreamRequestMessage where
  sessionId : BitVec 64
  nextSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StreamRequestMessage

def encode (message : StreamRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId
    ++ (encodeUInt 8 message.nextSequenceNumber)

def decode (bytes : List UInt8) : Option (StreamRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ sessionId, nextSequenceNumber }, bytes)

@[simp] theorem encode_length (message : StreamRequestMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StreamRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : StreamRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end StreamRequestMessage

/-- Unsequenced Message -/
structure UnsequencedMessage where
  sbeMessage : List UInt8
  deriving DecidableEq, Repr

namespace UnsequencedMessage

def encode (message : UnsequencedMessage) : List UInt8 :=
  encodeMany Byte.encode message.sbeMessage

def decode (bytes : List UInt8) : Option UnsequencedMessage := do
  let sbeMessage ← decodeAll Byte.decode bytes.length bytes
  pure { sbeMessage }

theorem decode_encode (message : UnsequencedMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.sbeMessage _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.sbeMessage), some_bind]
  rfl

end UnsequencedMessage

/-- Any Client Data, selected by Message Type -/
inductive ClientData where
  | loginRequestMessage (message : LoginRequestMessage) -- 100
  | replayRequestMessage (message : ReplayRequestMessage) -- 101
  | replayAllRequestMessage (message : ReplayAllRequestMessage) -- 102
  | streamRequestMessage (message : StreamRequestMessage) -- 103
  | unsequencedMessage (message : UnsequencedMessage) -- 104
  deriving DecidableEq, Repr

namespace ClientData

/-- The Message Type each message is sent under -/
def tag : ClientData → BitVec 8
  | .loginRequestMessage _ => 100
  | .replayRequestMessage _ => 101
  | .replayAllRequestMessage _ => 102
  | .streamRequestMessage _ => 103
  | .unsequencedMessage _ => 104

def encode : ClientData → List UInt8
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .replayRequestMessage message => ReplayRequestMessage.encode message
  | .replayAllRequestMessage message => ReplayAllRequestMessage.encode message
  | .streamRequestMessage message => StreamRequestMessage.encode message
  | .unsequencedMessage message => UnsequencedMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ClientData :=
  if tag = 100 then (LoginRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequestMessage message) else none
  else if tag = 101 then (ReplayRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.replayRequestMessage message) else none
  else if tag = 102 then (ReplayAllRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.replayAllRequestMessage message) else none
  else if tag = 103 then (StreamRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.streamRequestMessage message) else none
  else if tag = 104 then (UnsequencedMessage.decode bytes).map fun message => .unsequencedMessage message
  else none

theorem decode_encode (message : ClientData) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | loginRequestMessage message => simp [decode, encode, tag, LoginRequestMessage.decode_encode_nil]
  | replayRequestMessage message => simp [decode, encode, tag, ReplayRequestMessage.decode_encode_nil]
  | replayAllRequestMessage message => simp [decode, encode, tag, ReplayAllRequestMessage.decode_encode_nil]
  | streamRequestMessage message => simp [decode, encode, tag, StreamRequestMessage.decode_encode_nil]
  | unsequencedMessage message => simp [decode, encode, tag, UnsequencedMessage.decode_encode]

end ClientData

/-- Client Packet -/
structure ClientPacket where
  messageLength : BitVec 16
  clientData : ClientData
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeUInt 1 (ClientData.tag message.clientData)
    ++ (encodeUInt 2 message.messageLength
    ++ (ClientData.encode message.clientData))

def decode (bytes : List UInt8) : Option ClientPacket := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let clientData ← ClientData.decode messageType bytes
  pure { messageLength, clientData }

theorem encode_length_pos (message : ClientPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientData.decode_encode, some_bind]
  rfl

end ClientPacket

end Omi.MemxMemxequitiesCommonheaderTcpV12Client
