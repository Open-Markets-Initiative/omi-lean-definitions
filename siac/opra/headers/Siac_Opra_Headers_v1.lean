import Wire

/-!
# The Securities Industry Automation Corporation Headers v1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.SiacOpraHeadersUdpV1

/-- Retransmission Indicator: one byte code -/
def RetransmissionIndicator.codes : List UInt8 :=
  [0x20, 0x56]

inductive RetransmissionIndicator where
  | notRetransmitted -- Not Retransmitted
  | retransmitted -- Retransmitted
  | unlisted (byte : { byte : UInt8 // byte ∉ RetransmissionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetransmissionIndicator

def toByte : RetransmissionIndicator → UInt8
  | .notRetransmitted => 0x20
  | .retransmitted => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RetransmissionIndicator :=
  if byte = 0x20 then .notRetransmitted
  else .retransmitted

def ofByte (byte : UInt8) : RetransmissionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetransmissionIndicator) : ofByte value.toByte = value := by
  cases value with
  | notRetransmitted => decide
  | retransmitted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RetransmissionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetransmissionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RetransmissionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RetransmissionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RetransmissionIndicator

/-- Participant Id: one byte code -/
def ParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x48, 0x49, 0x4A, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x54, 0x55, 0x57, 0x58, 0x5A]

inductive ParticipantId where
  | amex -- Amex
  | box -- Box
  | cboe -- Cboe
  | emerald -- Emerald
  | edgx -- Edgx
  | gemx -- Gemx
  | ise -- Ise
  | mrx -- Mrx
  | miax -- Miax
  | nyse -- Nyse
  | opra -- Opra
  | pearl -- Pearl
  | nasd -- Nasd
  | bx -- Bx
  | memx -- Memx
  | c2 -- C2
  | phlx -- Phlx
  | bats -- Bats
  | unlisted (byte : { byte : UInt8 // byte ∉ ParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ParticipantId

def toByte : ParticipantId → UInt8
  | .amex => 0x41
  | .box => 0x42
  | .cboe => 0x43
  | .emerald => 0x44
  | .edgx => 0x45
  | .gemx => 0x48
  | .ise => 0x49
  | .mrx => 0x4A
  | .miax => 0x4D
  | .nyse => 0x4E
  | .opra => 0x4F
  | .pearl => 0x50
  | .nasd => 0x51
  | .bx => 0x54
  | .memx => 0x55
  | .c2 => 0x57
  | .phlx => 0x58
  | .bats => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ParticipantId :=
  if byte = 0x41 then .amex
  else if byte = 0x42 then .box
  else if byte = 0x43 then .cboe
  else if byte = 0x44 then .emerald
  else if byte = 0x45 then .edgx
  else if byte = 0x48 then .gemx
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .mrx
  else if byte = 0x4D then .miax
  else if byte = 0x4E then .nyse
  else if byte = 0x4F then .opra
  else if byte = 0x50 then .pearl
  else if byte = 0x51 then .nasd
  else if byte = 0x54 then .bx
  else if byte = 0x55 then .memx
  else if byte = 0x57 then .c2
  else if byte = 0x58 then .phlx
  else .bats

def ofByte (byte : UInt8) : ParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ParticipantId) : ofByte value.toByte = value := by
  cases value with
  | amex => decide
  | box => decide
  | cboe => decide
  | emerald => decide
  | edgx => decide
  | gemx => decide
  | ise => decide
  | mrx => decide
  | miax => decide
  | nyse => decide
  | opra => decide
  | pearl => decide
  | nasd => decide
  | bx => decide
  | memx => decide
  | c2 => decide
  | phlx => decide
  | bats => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ParticipantId

/-- Control Message Type: one byte code -/
def ControlMessageType.codes : List UInt8 :=
  [0x43, 0x45, 0x46, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50]

inductive ControlMessageType where
  | startOfDay -- Start Of Day
  | startOfSummary -- Start Of Summary
  | endOfSummary -- End Of Summary
  | endOfDay -- End Of Day
  | resetBlockSequenceNumber -- Reset Block Sequence Number
  | startOfOpenInterest -- Start Of Open Interest
  | endOfOpenInterest -- End Of Open Interest
  | lineIntegrity -- Line Integrity
  | disasterRecoveryDataCenterActivation -- Disaster Recovery Data Center Activation
  | unlisted (byte : { byte : UInt8 // byte ∉ ControlMessageType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ControlMessageType

def toByte : ControlMessageType → UInt8
  | .startOfDay => 0x43
  | .startOfSummary => 0x45
  | .endOfSummary => 0x46
  | .endOfDay => 0x4A
  | .resetBlockSequenceNumber => 0x4B
  | .startOfOpenInterest => 0x4C
  | .endOfOpenInterest => 0x4D
  | .lineIntegrity => 0x4E
  | .disasterRecoveryDataCenterActivation => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ControlMessageType :=
  if byte = 0x43 then .startOfDay
  else if byte = 0x45 then .startOfSummary
  else if byte = 0x46 then .endOfSummary
  else if byte = 0x4A then .endOfDay
  else if byte = 0x4B then .resetBlockSequenceNumber
  else if byte = 0x4C then .startOfOpenInterest
  else if byte = 0x4D then .endOfOpenInterest
  else if byte = 0x4E then .lineIntegrity
  else .disasterRecoveryDataCenterActivation

def ofByte (byte : UInt8) : ControlMessageType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ControlMessageType) : ofByte value.toByte = value := by
  cases value with
  | startOfDay => decide
  | startOfSummary => decide
  | endOfSummary => decide
  | endOfDay => decide
  | resetBlockSequenceNumber => decide
  | startOfOpenInterest => decide
  | endOfOpenInterest => decide
  | lineIntegrity => decide
  | disasterRecoveryDataCenterActivation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ControlMessageType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ControlMessageType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ControlMessageType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ControlMessageType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ControlMessageType

/-- Block Timestamp: 8 bytes -/
structure BlockTimestamp where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace BlockTimestamp

def encode (message : BlockTimestamp) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (BlockTimestamp × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : BlockTimestamp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BlockTimestamp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BlockTimestamp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BlockTimestamp

/-- Administrative Message -/
structure AdministrativeMessage where
  messageType : Alpha 1
  messageIndicator : Alpha 1
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 32
  messageData : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace AdministrativeMessage

def encode (message : AdministrativeMessage) : List UInt8 :=
  Alpha.encode message.messageType
    ++ (Alpha.encode message.messageIndicator
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.messageData.val.length)
    ++ (encodeMany Byte.encode message.messageData.val)))))

def decode (bytes : List UInt8) : Option (AdministrativeMessage × List UInt8) := do
  let (messageType, bytes) ← Alpha.decode 1 bytes
  let (messageIndicator, bytes) ← Alpha.decode 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (messageDataLength, bytes) ← decodeUInt 2 bytes
  let (messageData_, bytes) ← decodeMany Byte.decode messageDataLength.toNat bytes
  if fits_messageData : messageData_.length < 256 ^ 2 then
    pure ({ messageType, messageIndicator, transactionId, participantReferenceNumber, messageData := ⟨messageData_, fits_messageData⟩ }, bytes)
  else none

theorem encode_length_pos (message : AdministrativeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AdministrativeMessage) : (encode message).length ≤ 65547 := by
  have bound_messageData := message.messageData.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : AdministrativeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.messageData.length_lt]
  rfl

end AdministrativeMessage

/-- Control Message: 10 bytes -/
structure ControlMessage where
  controlMessageType : ControlMessageType
  messageIndicator : Alpha 1
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 32
  deriving DecidableEq, Repr

namespace ControlMessage

def encode (message : ControlMessage) : List UInt8 :=
  ControlMessageType.encode message.controlMessageType
    ++ (Alpha.encode message.messageIndicator
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 4 message.participantReferenceNumber)))

def decode (bytes : List UInt8) : Option (ControlMessage × List UInt8) := do
  let (controlMessageType, bytes) ← ControlMessageType.decode bytes
  let (messageIndicator, bytes) ← Alpha.decode 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  pure ({ controlMessageType, messageIndicator, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : ControlMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, ControlMessageType.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ControlMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ControlMessageType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ControlMessage

/-- Any Payload, selected by Message Category -/
inductive Payload where
  | administrativeMessage (message : AdministrativeMessage) -- "C" 0x43
  | controlMessage (message : ControlMessage) -- "H" 0x48
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Category each message is sent under -/
def tag : Payload → BitVec 8
  | .administrativeMessage _ => 67
  | .controlMessage _ => 72

def encode : Payload → List UInt8
  | .administrativeMessage message => AdministrativeMessage.encode message
  | .controlMessage message => ControlMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 65547 := by
  cases message with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega
  | controlMessage inner =>
    simp only [encode, ControlMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 67 then (AdministrativeMessage.decode bytes).map fun (message, rest) => (.administrativeMessage message, rest)
  else if tag = 72 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  participantId : ParticipantId
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (messageCategory, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageCategory bytes
  pure ({ participantId, payload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [ParticipantId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 65549 := by
  unfold encode
  cases message.payload with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | controlMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length, ControlMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  version : BitVec 8
  blockSize : BitVec 16
  dataFeedIndicator : Alpha 1
  retransmissionIndicator : RetransmissionIndicator
  sessionIndicator : BitVec 8
  blockSequenceNumber : BitVec 32
  blockTimestamp : BlockTimestamp
  blockChecksum : BitVec 16
  message : Bounded 1 Message
  blockPadByte : Capped 1
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.version
    ++ (encodeUInt 2 message.blockSize
    ++ (Alpha.encode message.dataFeedIndicator
    ++ (RetransmissionIndicator.encode message.retransmissionIndicator
    ++ (encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.blockSequenceNumber
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (BlockTimestamp.encode message.blockTimestamp
    ++ (encodeUInt 2 message.blockChecksum
    ++ (encodeMany Message.encode message.message.val
    ++ (message.blockPadByte.val))))))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (version, bytes) ← decodeUInt 1 bytes
  let (blockSize, bytes) ← decodeUInt 2 bytes
  let (dataFeedIndicator, bytes) ← Alpha.decode 1 bytes
  let (retransmissionIndicator, bytes) ← RetransmissionIndicator.decode bytes
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (messagesInBlock, bytes) ← decodeUInt 1 bytes
  let (blockTimestamp, bytes) ← BlockTimestamp.decode bytes
  let (blockChecksum, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messagesInBlock.toNat bytes
  let blockPadByte_ := bytes
  if fits_message : message_.length < 256 ^ 1 then
    if fits_blockPadByte : blockPadByte_.length ≤ 1 then
      pure { version, blockSize, dataFeedIndicator, retransmissionIndicator, sessionIndicator, blockSequenceNumber, blockTimestamp, blockChecksum, message := ⟨message_, fits_message⟩, blockPadByte := ⟨blockPadByte_, fits_blockPadByte⟩ }
    else none
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 16715017 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 65549 Message.encode_length_le message.message.val
  have bound_blockPadByte := message.blockPadByte.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIndicator.encode_length, BlockTimestamp.encode_length]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [RetransmissionIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [BlockTimestamp.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt, dite_eq_left message.blockPadByte.length_le]
  rfl

end Packet

end Omi.SiacOpraHeadersUdpV1
