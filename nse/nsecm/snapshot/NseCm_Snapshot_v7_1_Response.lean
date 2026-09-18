import Omi.Wire

/-!
# National Stock Exchange of India Ltd Mtbt Order Book Snapshot Recovery v7.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NseNsecmSnapshotBinaryV71Response

/-- Request Status: one byte code -/
def RequestStatus.codes : List UInt8 :=
  [0x53, 0x45]

inductive RequestStatus where
  | success -- Success
  | error -- Error
  | unlisted (byte : { byte : UInt8 // byte ∉ RequestStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RequestStatus

def toByte : RequestStatus → UInt8
  | .success => 0x53
  | .error => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RequestStatus :=
  if byte = 0x53 then .success
  else .error

def ofByte (byte : UInt8) : RequestStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RequestStatus) : ofByte value.toByte = value := by
  cases value with
  | success => decide
  | error => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RequestStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RequestStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RequestStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RequestStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RequestStatus

/-- Stream Header: 8 bytes -/
structure StreamHeader where
  messageLength : BitVec 16
  streamId : BitVec 16
  sequenceNumber : BitVec 32
  deriving DecidableEq, Repr

namespace StreamHeader

def encode (message : StreamHeader) : List UInt8 :=
  encodeUIntLE 2 message.messageLength
    ++ (encodeUIntLE 2 message.streamId
    ++ (encodeUIntLE 4 message.sequenceNumber))

def decode (bytes : List UInt8) : Option (StreamHeader × List UInt8) := do
  let (messageLength, bytes) ← decodeUIntLE 2 bytes
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageLength, streamId, sequenceNumber }, bytes)

@[simp] theorem encode_length (message : StreamHeader) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : StreamHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StreamHeader

/-- Order Book Snapshot Recovery Response Message: 1 bytes -/
structure OrderBookSnapshotRecoveryResponseMessage where
  requestStatus : RequestStatus
  deriving DecidableEq, Repr

namespace OrderBookSnapshotRecoveryResponseMessage

def encode (message : OrderBookSnapshotRecoveryResponseMessage) : List UInt8 :=
  RequestStatus.encode message.requestStatus

def decode (bytes : List UInt8) : Option (OrderBookSnapshotRecoveryResponseMessage × List UInt8) := do
  let (requestStatus, bytes) ← RequestStatus.decode bytes
  pure ({ requestStatus }, bytes)

@[simp] theorem encode_length (message : OrderBookSnapshotRecoveryResponseMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [RequestStatus.encode_length]

theorem encode_length_pos (message : OrderBookSnapshotRecoveryResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookSnapshotRecoveryResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RequestStatus.decode_encode, some_bind]
  rfl

end OrderBookSnapshotRecoveryResponseMessage

/-- Any Response Payload, selected by Response Message Type -/
inductive ResponsePayload where
  | orderBookSnapshotRecoveryResponseMessage (message : OrderBookSnapshotRecoveryResponseMessage) -- 'B' 0x42
  deriving DecidableEq, Repr

namespace ResponsePayload

/-- The Response Message Type each message is sent under -/
def tag : ResponsePayload → BitVec 8
  | .orderBookSnapshotRecoveryResponseMessage _ => 66

def encode : ResponsePayload → List UInt8
  | .orderBookSnapshotRecoveryResponseMessage message => OrderBookSnapshotRecoveryResponseMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ResponsePayload × List UInt8) :=
  if tag = 66 then (OrderBookSnapshotRecoveryResponseMessage.decode bytes).map fun (message, rest) => (.orderBookSnapshotRecoveryResponseMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ResponsePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ResponsePayload

/-- Response Packet -/
structure ResponsePacket where
  streamHeader : StreamHeader
  responsePayload : ResponsePayload
  deriving DecidableEq, Repr

namespace ResponsePacket

def encode (message : ResponsePacket) : List UInt8 :=
  StreamHeader.encode message.streamHeader
    ++ (encodeUInt 1 (ResponsePayload.tag message.responsePayload)
    ++ (ResponsePayload.encode message.responsePayload))

def decode (bytes : List UInt8) : Option (ResponsePacket × List UInt8) := do
  let (streamHeader, bytes) ← StreamHeader.decode bytes
  let (responseMessageType, bytes) ← decodeUInt 1 bytes
  let (responsePayload, bytes) ← ResponsePayload.decode responseMessageType bytes
  pure ({ streamHeader, responsePayload }, bytes)

theorem encode_length_pos (message : ResponsePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [StreamHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ResponsePacket) : (encode message).length ≤ 10 := by
  unfold encode
  cases message.responsePayload with
  | orderBookSnapshotRecoveryResponseMessage inner =>
    simp only [ResponsePayload.encode, List.length_append, ← Nat.add_assoc, StreamHeader.encode_length, encodeUInt_length, OrderBookSnapshotRecoveryResponseMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ResponsePacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, StreamHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ResponsePayload.decode_encode, some_bind]
  rfl

end ResponsePacket

end Omi.NseNsecmSnapshotBinaryV71Response
