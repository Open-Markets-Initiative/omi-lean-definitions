import Omi.Wire

/-!
# National Stock Exchange of India Ltd Mtbt Tick Data Recovery v6.8

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NseNsecomRecoveryBinaryV68Client

/-- Tick Data Recovery Request Message: 10 bytes -/
structure TickDataRecoveryRequestMessage where
  streamId : BitVec 16
  startSequenceNumber : BitVec 32
  endSequenceNumber : BitVec 32
  deriving DecidableEq, Repr

namespace TickDataRecoveryRequestMessage

def encode (message : TickDataRecoveryRequestMessage) : List UInt8 :=
  encodeUIntLE 2 message.streamId
    ++ (encodeUIntLE 4 message.startSequenceNumber
    ++ (encodeUIntLE 4 message.endSequenceNumber))

def decode (bytes : List UInt8) : Option (TickDataRecoveryRequestMessage × List UInt8) := do
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (startSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (endSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  pure ({ streamId, startSequenceNumber, endSequenceNumber }, bytes)

@[simp] theorem encode_length (message : TickDataRecoveryRequestMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TickDataRecoveryRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickDataRecoveryRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TickDataRecoveryRequestMessage

/-- Any Client Payload, selected by Client Message Type -/
inductive ClientPayload where
  | tickDataRecoveryRequestMessage (message : TickDataRecoveryRequestMessage) -- 'R' 0x52
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Client Message Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .tickDataRecoveryRequestMessage _ => 82

def encode : ClientPayload → List UInt8
  | .tickDataRecoveryRequestMessage message => TickDataRecoveryRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 10 := by
  cases message with
  | tickDataRecoveryRequestMessage inner =>
    simp only [encode, TickDataRecoveryRequestMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 82 then (TickDataRecoveryRequestMessage.decode bytes).map fun (message, rest) => (.tickDataRecoveryRequestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Packet -/
structure ClientPacket where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decode (bytes : List UInt8) : Option (ClientPacket × List UInt8) := do
  let (clientMessageType, bytes) ← decodeUInt 1 bytes
  let (clientPayload, bytes) ← ClientPayload.decode clientMessageType bytes
  pure ({ clientPayload }, bytes)

theorem encode_length_pos (message : ClientPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientPacket) : (encode message).length ≤ 11 := by
  unfold encode
  cases message.clientPayload with
  | tickDataRecoveryRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, TickDataRecoveryRequestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ClientPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

end ClientPacket

end Omi.NseNsecomRecoveryBinaryV68Client
