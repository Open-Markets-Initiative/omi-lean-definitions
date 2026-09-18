import Omi.Wire

/-!
# Aquis Exchange Market Data Replay v4.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.AquisAquisequitiesReplayAmdV41

/-- Login Message: 20 bytes -/
structure LoginMessage where
  username : Alpha 10
  password : Alpha 10
  deriving DecidableEq, Repr

namespace LoginMessage

def encode (message : LoginMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password)

def decode (bytes : List UInt8) : Option (LoginMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 10 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  pure ({ username, password }, bytes)

@[simp] theorem encode_length (message : LoginMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginMessage

/-- Replay Request Message: 8 bytes -/
structure ReplayRequestMessage where
  beginSeqNo : BitVec 32
  endSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayRequestMessage

def encode (message : ReplayRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.beginSeqNo
    ++ (encodeUIntLE 4 message.endSeqNo)

def decode (bytes : List UInt8) : Option (ReplayRequestMessage × List UInt8) := do
  let (beginSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ beginSeqNo, endSeqNo }, bytes)

@[simp] theorem encode_length (message : ReplayRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ReplayRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReplayRequestMessage

/-- Replay Response Message: 1 bytes -/
structure ReplayResponseMessage where
  responseCode : BitVec 8
  deriving DecidableEq, Repr

namespace ReplayResponseMessage

def encode (message : ReplayResponseMessage) : List UInt8 :=
  encodeUIntLE 1 message.responseCode

def decode (bytes : List UInt8) : Option (ReplayResponseMessage × List UInt8) := do
  let (responseCode, bytes) ← decodeUIntLE 1 bytes
  pure ({ responseCode }, bytes)

@[simp] theorem encode_length (message : ReplayResponseMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : ReplayResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReplayResponseMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | loginMessage (message : LoginMessage) -- 13
  | replayRequestMessage (message : ReplayRequestMessage) -- 14
  | replayResponseMessage (message : ReplayResponseMessage) -- 15
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 8
  | .loginMessage _ => 13
  | .replayRequestMessage _ => 14
  | .replayResponseMessage _ => 15

def encode : Payload → List UInt8
  | .loginMessage message => LoginMessage.encode message
  | .replayRequestMessage message => ReplayRequestMessage.encode message
  | .replayResponseMessage message => ReplayResponseMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 13 then (LoginMessage.decode bytes).map fun (message, rest) => (.loginMessage message, rest)
  else if tag = 14 then (ReplayRequestMessage.decode bytes).map fun (message, rest) => (.replayRequestMessage message, rest)
  else if tag = 15 then (ReplayResponseMessage.decode bytes).map fun (message, rest) => (.replayResponseMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  seqNo : BitVec 32
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 4 message.seqNo
    ++ (Payload.encode message.payload)

def decodeBody (msgType : BitVec 8) (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (seqNo, bytes) ← decodeUInt 4 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ seqNo, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (Payload.tag message.payload) (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 1 := by
  unfold encodeBody
  cases message.payload with
  | loginMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginMessage.encode_length]
    omega
  | replayRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayRequestMessage.encode_length]
    omega
  | replayResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayResponseMessage.encode_length]
    omega

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body and checked on decode; Msg Type is read ahead of it -/
def encode (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeFramed 1 2 encodeBody message)

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  decodeFramed 1 2 (decodeBody msgType) bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  exact decodeFramed_encodeFramed 1 2 encodeBody (decodeBody (Payload.tag message.payload)) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option Packet := do
  let message ← decodeAll Message.decode bytes.length bytes
  pure { message }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end Packet

end Omi.AquisAquisequitiesReplayAmdV41
