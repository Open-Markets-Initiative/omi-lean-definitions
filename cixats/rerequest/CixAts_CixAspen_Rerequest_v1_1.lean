import Omi.Wire

/-!
# CIX Trading Inc. CIX Udp Rerequest v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CixatsCixaspenRerequestAspenV11

/-- Feed Identifier: one byte code -/
def FeedIdentifier.codes : List UInt8 :=
  [0x41, 0x56, 0x4D, 0x42, 0x57, 0x4E]

inductive FeedIdentifier where
  | aspen -- Aspen
  | aspenVert -- Aspen Vert
  | midpoint -- Midpoint
  | aspenUat -- Aspen Uat
  | aspenVertUat -- Aspen Vert Uat
  | midpointUat -- Midpoint Uat
  | unlisted (byte : { byte : UInt8 // byte ∉ FeedIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FeedIdentifier

def toByte : FeedIdentifier → UInt8
  | .aspen => 0x41
  | .aspenVert => 0x56
  | .midpoint => 0x4D
  | .aspenUat => 0x42
  | .aspenVertUat => 0x57
  | .midpointUat => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FeedIdentifier :=
  if byte = 0x41 then .aspen
  else if byte = 0x56 then .aspenVert
  else if byte = 0x4D then .midpoint
  else if byte = 0x42 then .aspenUat
  else if byte = 0x57 then .aspenVertUat
  else .midpointUat

def ofByte (byte : UInt8) : FeedIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FeedIdentifier) : ofByte value.toByte = value := by
  cases value with
  | aspen => decide
  | aspenVert => decide
  | midpoint => decide
  | aspenUat => decide
  | aspenVertUat => decide
  | midpointUat => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FeedIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FeedIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FeedIdentifier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FeedIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FeedIdentifier

/-- Rerequest Header: 20 bytes -/
structure RerequestHeader where
  marketDayIdentifier : Alpha 9
  feedIdentifier : FeedIdentifier
  sequence : BitVec 64
  count : BitVec 16
  deriving DecidableEq, Repr

namespace RerequestHeader

def encode (message : RerequestHeader) : List UInt8 :=
  Alpha.encode message.marketDayIdentifier
    ++ (FeedIdentifier.encode message.feedIdentifier
    ++ (encodeUIntLE 8 message.sequence
    ++ (encodeUIntLE 2 message.count)))

def decode (bytes : List UInt8) : Option (RerequestHeader × List UInt8) := do
  let (marketDayIdentifier, bytes) ← Alpha.decode 9 bytes
  let (feedIdentifier, bytes) ← FeedIdentifier.decode bytes
  let (sequence, bytes) ← decodeUIntLE 8 bytes
  let (count, bytes) ← decodeUIntLE 2 bytes
  pure ({ marketDayIdentifier, feedIdentifier, sequence, count }, bytes)

@[simp] theorem encode_length (message : RerequestHeader) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, FeedIdentifier.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : RerequestHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RerequestHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FeedIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RerequestHeader

/-- Packet: 20 bytes -/
structure Packet where
  rerequestHeader : RerequestHeader
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  RerequestHeader.encode message.rerequestHeader

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (rerequestHeader, bytes) ← RerequestHeader.decode bytes
  pure ({ rerequestHeader }, bytes)

@[simp] theorem encode_length (message : Packet) : (encode message).length = 20 := by
  unfold encode
  simp only [RerequestHeader.encode_length]

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RerequestHeader.decode_encode, some_bind]
  rfl

end Packet

end Omi.CixatsCixaspenRerequestAspenV11
