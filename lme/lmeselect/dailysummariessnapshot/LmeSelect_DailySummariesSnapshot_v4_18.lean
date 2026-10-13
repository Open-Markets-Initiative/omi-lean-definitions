import Wire

/-!
# The London Metal Exchange LMEsource DailySummaries Refresh v4.18

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LmeLmeselectDailysummariessnapshotLmesourceV418

/-- Open Interest Type: one byte code -/
def OpenInterestType.codes : List UInt8 :=
  [0x45, 0x4D]

inductive OpenInterestType where
  | exchange -- Exchange
  | market -- Market
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenInterestType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenInterestType

def toByte : OpenInterestType → UInt8
  | .exchange => 0x45
  | .market => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenInterestType :=
  if byte = 0x45 then .exchange
  else .market

def ofByte (byte : UInt8) : OpenInterestType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenInterestType) : ofByte value.toByte = value := by
  cases value with
  | exchange => decide
  | market => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenInterestType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenInterestType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenInterestType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpenInterestType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpenInterestType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenInterestType

/-- Contract Type: one byte code -/
def ContractType.codes : List UInt8 :=
  [0x46, 0x4F]

inductive ContractType where
  | future -- Future
  | option -- Option
  | unlisted (byte : { byte : UInt8 // byte ∉ ContractType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContractType

def toByte : ContractType → UInt8
  | .future => 0x46
  | .option => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContractType :=
  if byte = 0x46 then .future
  else .option

def ofByte (byte : UInt8) : ContractType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContractType) : ofByte value.toByte = value := by
  cases value with
  | future => decide
  | option => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContractType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContractType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContractType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ContractType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ContractType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContractType

/-- Calculation Type: one byte code -/
def CalculationType.codes : List UInt8 :=
  [0x44, 0x49]

inductive CalculationType where
  | daily -- Daily
  | intraday -- Intraday
  | unlisted (byte : { byte : UInt8 // byte ∉ CalculationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CalculationType

def toByte : CalculationType → UInt8
  | .daily => 0x44
  | .intraday => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CalculationType :=
  if byte = 0x44 then .daily
  else .intraday

def ofByte (byte : UInt8) : CalculationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CalculationType) : ofByte value.toByte = value := by
  cases value with
  | daily => decide
  | intraday => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CalculationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CalculationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CalculationType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CalculationType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CalculationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CalculationType

/-- Sequence Reset Message: 4 bytes -/
structure SequenceResetMessage where
  newSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceResetMessage

def encode (message : SequenceResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.newSeqNo

def decode (bytes : List UInt8) : Option (SequenceResetMessage × List UInt8) := do
  let (newSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ newSeqNo }, bytes)

@[simp] theorem encode_length (message : SequenceResetMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceResetMessage

/-- Open Interest Message: 32 bytes -/
structure OpenInterestMessage where
  businessDate : BitVec 32
  openInterestType : OpenInterestType
  instrumentId : BitVec 64
  productCode : Alpha 2
  contractCode : Alpha 12
  contractType : ContractType
  volume : BitVec 32
  deriving DecidableEq, Repr

namespace OpenInterestMessage

def encode (message : OpenInterestMessage) : List UInt8 :=
  encodeUIntLE 4 message.businessDate
    ++ (OpenInterestType.encode message.openInterestType
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.contractCode
    ++ (ContractType.encode message.contractType
    ++ (encodeUIntLE 4 message.volume))))))

def decode (bytes : List UInt8) : Option (OpenInterestMessage × List UInt8) := do
  let (businessDate, bytes) ← decodeUIntLE 4 bytes
  let (openInterestType, bytes) ← OpenInterestType.decode bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (contractCode, bytes) ← Alpha.decode 12 bytes
  let (contractType, bytes) ← ContractType.decode bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  pure ({ businessDate, openInterestType, instrumentId, productCode, contractCode, contractType, volume }, bytes)

@[simp] theorem encode_length (message : OpenInterestMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OpenInterestType.encode_length, Alpha.encode_length, ContractType.encode_length]

theorem encode_length_pos (message : OpenInterestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenInterestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OpenInterestType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractType.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OpenInterestMessage

/-- Date Bands: 12 bytes -/
structure DateBands where
  fromDate : BitVec 32
  toDate : BitVec 32
  volume : BitVec 32
  deriving DecidableEq, Repr

namespace DateBands

def encode (message : DateBands) : List UInt8 :=
  encodeUIntLE 4 message.fromDate
    ++ (encodeUIntLE 4 message.toDate
    ++ (encodeUIntLE 4 message.volume))

def decode (bytes : List UInt8) : Option (DateBands × List UInt8) := do
  let (fromDate, bytes) ← decodeUIntLE 4 bytes
  let (toDate, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  pure ({ fromDate, toDate, volume }, bytes)

@[simp] theorem encode_length (message : DateBands) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DateBands) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DateBands) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DateBands

/-- Open Interest Band Message -/
structure OpenInterestBandMessage where
  businessDate : BitVec 32
  productCode : Alpha 2
  contractCode : Alpha 12
  contractType : ContractType
  currencyCode : Alpha 3
  dateBands : Bounded 4 DateBands
  deriving DecidableEq, Repr

namespace OpenInterestBandMessage

def encode (message : OpenInterestBandMessage) : List UInt8 :=
  encodeUIntLE 4 message.businessDate
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.contractCode
    ++ (ContractType.encode message.contractType
    ++ (Alpha.encode message.currencyCode
    ++ (encodeUIntLE 4 (BitVec.ofNat (8 * 4) message.dateBands.val.length)
    ++ (encodeMany DateBands.encode message.dateBands.val))))))

def decode (bytes : List UInt8) : Option (OpenInterestBandMessage × List UInt8) := do
  let (businessDate, bytes) ← decodeUIntLE 4 bytes
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (contractCode, bytes) ← Alpha.decode 12 bytes
  let (contractType, bytes) ← ContractType.decode bytes
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (dateBandCount, bytes) ← decodeUIntLE 4 bytes
  let (dateBands_, bytes) ← decodeMany DateBands.decode dateBandCount.toNat bytes
  if fits_dateBands : dateBands_.length < 256 ^ 4 then
    pure ({ businessDate, productCode, contractCode, contractType, currencyCode, dateBands := ⟨dateBands_, fits_dateBands⟩ }, bytes)
  else none

theorem encode_length_pos (message : OpenInterestBandMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OpenInterestBandMessage) : (encode message).length ≤ 51539607566 := by
  have bound_dateBands := message.dateBands.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, ContractType.encode_length, encodeMany_length_const DateBands.encode 12 DateBands.encode_length]
  omega

@[simp] theorem decode_encode (message : OpenInterestBandMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 DateBands.encode DateBands.decode DateBands.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dateBands.length_lt]
  rfl

end OpenInterestBandMessage

/-- Long Prompt Dates: 14 bytes -/
structure LongPromptDates where
  promptDateLabel : Alpha 6
  expiryDate : BitVec 32
  participantCount : BitVec 32
  deriving DecidableEq, Repr

namespace LongPromptDates

def encode (message : LongPromptDates) : List UInt8 :=
  Alpha.encode message.promptDateLabel
    ++ (encodeUIntLE 4 message.expiryDate
    ++ (encodeUIntLE 4 message.participantCount))

def decode (bytes : List UInt8) : Option (LongPromptDates × List UInt8) := do
  let (promptDateLabel, bytes) ← Alpha.decode 6 bytes
  let (expiryDate, bytes) ← decodeUIntLE 4 bytes
  let (participantCount, bytes) ← decodeUIntLE 4 bytes
  pure ({ promptDateLabel, expiryDate, participantCount }, bytes)

@[simp] theorem encode_length (message : LongPromptDates) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : LongPromptDates) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongPromptDates) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LongPromptDates

/-- Long Position Bands -/
structure LongPositionBands where
  longPositionLowerValue : BitVec 64
  longPositionUpperValue : BitVec 64
  longPromptDates : Bounded 4 LongPromptDates
  deriving DecidableEq, Repr

namespace LongPositionBands

def encode (message : LongPositionBands) : List UInt8 :=
  encodeUIntLE 8 message.longPositionLowerValue
    ++ (encodeUIntLE 8 message.longPositionUpperValue
    ++ (encodeUIntLE 4 (BitVec.ofNat (8 * 4) message.longPromptDates.val.length)
    ++ (encodeMany LongPromptDates.encode message.longPromptDates.val)))

def decode (bytes : List UInt8) : Option (LongPositionBands × List UInt8) := do
  let (longPositionLowerValue, bytes) ← decodeUIntLE 8 bytes
  let (longPositionUpperValue, bytes) ← decodeUIntLE 8 bytes
  let (longPositionPromptDateCount, bytes) ← decodeUIntLE 4 bytes
  let (longPromptDates_, bytes) ← decodeMany LongPromptDates.decode longPositionPromptDateCount.toNat bytes
  if fits_longPromptDates : longPromptDates_.length < 256 ^ 4 then
    pure ({ longPositionLowerValue, longPositionUpperValue, longPromptDates := ⟨longPromptDates_, fits_longPromptDates⟩ }, bytes)
  else none

theorem encode_length_pos (message : LongPositionBands) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongPositionBands) : (encode message).length ≤ 60129542150 := by
  have bound_longPromptDates := message.longPromptDates.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const LongPromptDates.encode 14 LongPromptDates.encode_length]
  omega

@[simp] theorem decode_encode (message : LongPositionBands) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 LongPromptDates.encode LongPromptDates.decode LongPromptDates.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longPromptDates.length_lt]
  rfl

end LongPositionBands

/-- Short Prompt Dates: 14 bytes -/
structure ShortPromptDates where
  promptDateLabel : Alpha 6
  expiryDate : BitVec 32
  participantCount : BitVec 32
  deriving DecidableEq, Repr

namespace ShortPromptDates

def encode (message : ShortPromptDates) : List UInt8 :=
  Alpha.encode message.promptDateLabel
    ++ (encodeUIntLE 4 message.expiryDate
    ++ (encodeUIntLE 4 message.participantCount))

def decode (bytes : List UInt8) : Option (ShortPromptDates × List UInt8) := do
  let (promptDateLabel, bytes) ← Alpha.decode 6 bytes
  let (expiryDate, bytes) ← decodeUIntLE 4 bytes
  let (participantCount, bytes) ← decodeUIntLE 4 bytes
  pure ({ promptDateLabel, expiryDate, participantCount }, bytes)

@[simp] theorem encode_length (message : ShortPromptDates) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : ShortPromptDates) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortPromptDates) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ShortPromptDates

/-- Short Position Bands -/
structure ShortPositionBands where
  shortPositionLowerValue : BitVec 64
  shortPositionUpperValue : BitVec 64
  shortPromptDates : Bounded 4 ShortPromptDates
  deriving DecidableEq, Repr

namespace ShortPositionBands

def encode (message : ShortPositionBands) : List UInt8 :=
  encodeUIntLE 8 message.shortPositionLowerValue
    ++ (encodeUIntLE 8 message.shortPositionUpperValue
    ++ (encodeUIntLE 4 (BitVec.ofNat (8 * 4) message.shortPromptDates.val.length)
    ++ (encodeMany ShortPromptDates.encode message.shortPromptDates.val)))

def decode (bytes : List UInt8) : Option (ShortPositionBands × List UInt8) := do
  let (shortPositionLowerValue, bytes) ← decodeUIntLE 8 bytes
  let (shortPositionUpperValue, bytes) ← decodeUIntLE 8 bytes
  let (shortPositionPromptDateCount, bytes) ← decodeUIntLE 4 bytes
  let (shortPromptDates_, bytes) ← decodeMany ShortPromptDates.decode shortPositionPromptDateCount.toNat bytes
  if fits_shortPromptDates : shortPromptDates_.length < 256 ^ 4 then
    pure ({ shortPositionLowerValue, shortPositionUpperValue, shortPromptDates := ⟨shortPromptDates_, fits_shortPromptDates⟩ }, bytes)
  else none

theorem encode_length_pos (message : ShortPositionBands) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ShortPositionBands) : (encode message).length ≤ 60129542150 := by
  have bound_shortPromptDates := message.shortPromptDates.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const ShortPromptDates.encode 14 ShortPromptDates.encode_length]
  omega

@[simp] theorem decode_encode (message : ShortPositionBands) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 ShortPromptDates.encode ShortPromptDates.decode ShortPromptDates.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.shortPromptDates.length_lt]
  rfl

end ShortPositionBands

/-- Position Band Message -/
structure PositionBandMessage where
  businessDate : BitVec 32
  productCode : Alpha 2
  longPositionBands : Bounded 4 LongPositionBands
  shortPositionBands : Bounded 4 ShortPositionBands
  deriving DecidableEq, Repr

namespace PositionBandMessage

def encode (message : PositionBandMessage) : List UInt8 :=
  encodeUIntLE 4 message.businessDate
    ++ (Alpha.encode message.productCode
    ++ (encodeUIntLE 4 (BitVec.ofNat (8 * 4) message.longPositionBands.val.length)
    ++ (encodeUIntLE 4 (BitVec.ofNat (8 * 4) message.shortPositionBands.val.length)
    ++ (encodeMany LongPositionBands.encode message.longPositionBands.val
    ++ (encodeMany ShortPositionBands.encode message.shortPositionBands.val)))))

def decode (bytes : List UInt8) : Option (PositionBandMessage × List UInt8) := do
  let (businessDate, bytes) ← decodeUIntLE 4 bytes
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (longPositionBandCount, bytes) ← decodeUIntLE 4 bytes
  let (shortPositionBandCount, bytes) ← decodeUIntLE 4 bytes
  let (longPositionBands_, bytes) ← decodeMany LongPositionBands.decode longPositionBandCount.toNat bytes
  let (shortPositionBands_, bytes) ← decodeMany ShortPositionBands.decode shortPositionBandCount.toNat bytes
  if fits_longPositionBands : longPositionBands_.length < 256 ^ 4 then
    if fits_shortPositionBands : shortPositionBands_.length < 256 ^ 4 then
      pure ({ businessDate, productCode, longPositionBands := ⟨longPositionBands_, fits_longPositionBands⟩, shortPositionBands := ⟨shortPositionBands_, fits_shortPositionBands⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : PositionBandMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PositionBandMessage) : (encode message).length ≤ -68719476734 := by
  have bound_longPositionBands := message.longPositionBands.length_lt
  have bound_longPositionBands_items := encodeMany_length_le LongPositionBands.encode 60129542150 LongPositionBands.encode_length_le message.longPositionBands.val
  have bound_shortPositionBands := message.shortPositionBands.length_lt
  have bound_shortPositionBands_items := encodeMany_length_le ShortPositionBands.encode 60129542150 ShortPositionBands.encode_length_le message.shortPositionBands.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : PositionBandMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 4 LongPositionBands.encode LongPositionBands.decode LongPositionBands.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 ShortPositionBands.encode ShortPositionBands.decode ShortPositionBands.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.longPositionBands.length_lt, dite_eq_left message.shortPositionBands.length_lt]
  rfl

end PositionBandMessage

/-- Warrant Bands: 20 bytes -/
structure WarrantBands where
  lowerValue : BitVec 64
  upperValue : BitVec 64
  participantCount : BitVec 32
  deriving DecidableEq, Repr

namespace WarrantBands

def encode (message : WarrantBands) : List UInt8 :=
  encodeUIntLE 8 message.lowerValue
    ++ (encodeUIntLE 8 message.upperValue
    ++ (encodeUIntLE 4 message.participantCount))

def decode (bytes : List UInt8) : Option (WarrantBands × List UInt8) := do
  let (lowerValue, bytes) ← decodeUIntLE 8 bytes
  let (upperValue, bytes) ← decodeUIntLE 8 bytes
  let (participantCount, bytes) ← decodeUIntLE 4 bytes
  pure ({ lowerValue, upperValue, participantCount }, bytes)

@[simp] theorem encode_length (message : WarrantBands) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : WarrantBands) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WarrantBands) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end WarrantBands

/-- Warrant Band Message -/
structure WarrantBandMessage where
  businessDate : BitVec 32
  warrantBandType : Alpha 4
  productCode : Alpha 2
  unreportedWarrants : BitVec 64
  warrantBands : Bounded 4 WarrantBands
  deriving DecidableEq, Repr

namespace WarrantBandMessage

def encode (message : WarrantBandMessage) : List UInt8 :=
  encodeUIntLE 4 message.businessDate
    ++ (Alpha.encode message.warrantBandType
    ++ (Alpha.encode message.productCode
    ++ (encodeUIntLE 8 message.unreportedWarrants
    ++ (encodeUIntLE 4 (BitVec.ofNat (8 * 4) message.warrantBands.val.length)
    ++ (encodeMany WarrantBands.encode message.warrantBands.val)))))

def decode (bytes : List UInt8) : Option (WarrantBandMessage × List UInt8) := do
  let (businessDate, bytes) ← decodeUIntLE 4 bytes
  let (warrantBandType, bytes) ← Alpha.decode 4 bytes
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (unreportedWarrants, bytes) ← decodeUIntLE 8 bytes
  let (bandCount, bytes) ← decodeUIntLE 4 bytes
  let (warrantBands_, bytes) ← decodeMany WarrantBands.decode bandCount.toNat bytes
  if fits_warrantBands : warrantBands_.length < 256 ^ 4 then
    pure ({ businessDate, warrantBandType, productCode, unreportedWarrants, warrantBands := ⟨warrantBands_, fits_warrantBands⟩ }, bytes)
  else none

theorem encode_length_pos (message : WarrantBandMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : WarrantBandMessage) : (encode message).length ≤ 85899345922 := by
  have bound_warrantBands := message.warrantBands.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeMany_length_const WarrantBands.encode 20 WarrantBands.encode_length]
  omega

@[simp] theorem decode_encode (message : WarrantBandMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 WarrantBands.encode WarrantBands.decode WarrantBands.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.warrantBands.length_lt]
  rfl

end WarrantBandMessage

/-- Trading Volume Message: 36 bytes -/
structure TradingVolumeMessage where
  businessDate : BitVec 32
  tradeDate : BitVec 32
  calculationType : CalculationType
  instrumentId : BitVec 64
  productCode : Alpha 2
  contractCode : Alpha 12
  contractType : ContractType
  volume : BitVec 32
  deriving DecidableEq, Repr

namespace TradingVolumeMessage

def encode (message : TradingVolumeMessage) : List UInt8 :=
  encodeUIntLE 4 message.businessDate
    ++ (encodeUIntLE 4 message.tradeDate
    ++ (CalculationType.encode message.calculationType
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.contractCode
    ++ (ContractType.encode message.contractType
    ++ (encodeUIntLE 4 message.volume)))))))

def decode (bytes : List UInt8) : Option (TradingVolumeMessage × List UInt8) := do
  let (businessDate, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (calculationType, bytes) ← CalculationType.decode bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (contractCode, bytes) ← Alpha.decode 12 bytes
  let (contractType, bytes) ← ContractType.decode bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  pure ({ businessDate, tradeDate, calculationType, instrumentId, productCode, contractCode, contractType, volume }, bytes)

@[simp] theorem encode_length (message : TradingVolumeMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, CalculationType.encode_length, Alpha.encode_length, ContractType.encode_length]

theorem encode_length_pos (message : TradingVolumeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingVolumeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CalculationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractType.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradingVolumeMessage

/-- Refresh Complete Message: 4 bytes -/
structure RefreshCompleteMessage where
  lastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RefreshCompleteMessage

def encode (message : RefreshCompleteMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastSeqNum

def decode (bytes : List UInt8) : Option (RefreshCompleteMessage × List UInt8) := do
  let (lastSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ lastSeqNum }, bytes)

@[simp] theorem encode_length (message : RefreshCompleteMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : RefreshCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RefreshCompleteMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | sequenceResetMessage (message : SequenceResetMessage) -- 100
  | openInterestMessage (message : OpenInterestMessage) -- 420
  | openInterestBandMessage (message : OpenInterestBandMessage) -- 421
  | positionBandMessage (message : PositionBandMessage) -- 422
  | warrantBandMessage (message : WarrantBandMessage) -- 423
  | tradingVolumeMessage (message : TradingVolumeMessage) -- 424
  | refreshCompleteMessage (message : RefreshCompleteMessage) -- 203
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceResetMessage _ => 100
  | .openInterestMessage _ => 420
  | .openInterestBandMessage _ => 421
  | .positionBandMessage _ => 422
  | .warrantBandMessage _ => 423
  | .tradingVolumeMessage _ => 424
  | .refreshCompleteMessage _ => 203

def encode : Payload → List UInt8
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .openInterestMessage message => OpenInterestMessage.encode message
  | .openInterestBandMessage message => OpenInterestBandMessage.encode message
  | .positionBandMessage message => PositionBandMessage.encode message
  | .warrantBandMessage message => WarrantBandMessage.encode message
  | .tradingVolumeMessage message => TradingVolumeMessage.encode message
  | .refreshCompleteMessage message => RefreshCompleteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 85899345922 := by
  cases message with
  | sequenceResetMessage inner =>
    simp only [encode, SequenceResetMessage.encode_length]
    omega
  | openInterestMessage inner =>
    simp only [encode, OpenInterestMessage.encode_length]
    omega
  | openInterestBandMessage inner =>
    have bound_inner := OpenInterestBandMessage.encode_length_le inner
    simp only [encode]
    omega
  | positionBandMessage inner =>
    have bound_inner := PositionBandMessage.encode_length_le inner
    simp only [encode]
    omega
  | warrantBandMessage inner =>
    have bound_inner := WarrantBandMessage.encode_length_le inner
    simp only [encode]
    omega
  | tradingVolumeMessage inner =>
    simp only [encode, TradingVolumeMessage.encode_length]
    omega
  | refreshCompleteMessage inner =>
    simp only [encode, RefreshCompleteMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 100 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 420 then (OpenInterestMessage.decode bytes).map fun (message, rest) => (.openInterestMessage message, rest)
  else if tag = 421 then (OpenInterestBandMessage.decode bytes).map fun (message, rest) => (.openInterestBandMessage message, rest)
  else if tag = 422 then (PositionBandMessage.decode bytes).map fun (message, rest) => (.positionBandMessage message, rest)
  else if tag = 423 then (WarrantBandMessage.decode bytes).map fun (message, rest) => (.warrantBandMessage message, rest)
  else if tag = 424 then (TradingVolumeMessage.decode bytes).map fun (message, rest) => (.tradingVolumeMessage message, rest)
  else if tag = 203 then (RefreshCompleteMessage.decode bytes).map fun (message, rest) => (.refreshCompleteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Messages -/
structure Messages where
  msgSize : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Messages

def encode (message : Messages) : List UInt8 :=
  encodeUIntLE 2 message.msgSize
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decode (bytes : List UInt8) : Option (Messages × List UInt8) := do
  let (msgSize, bytes) ← decodeUIntLE 2 bytes
  let (msgType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ msgSize, payload }, bytes)

theorem encode_length_pos (message : Messages) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Messages) : (encode message).length ≤ 85899345926 := by
  unfold encode
  cases message.payload with
  | sequenceResetMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceResetMessage.encode_length]
    omega
  | openInterestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OpenInterestMessage.encode_length]
    omega
  | openInterestBandMessage inner =>
    have bound_inner := OpenInterestBandMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | positionBandMessage inner =>
    have bound_inner := PositionBandMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | warrantBandMessage inner =>
    have bound_inner := WarrantBandMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | tradingVolumeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradingVolumeMessage.encode_length]
    omega
  | refreshCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RefreshCompleteMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Messages) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Messages

/-- Packet -/
structure Packet where
  pktSize : BitVec 16
  filler : Alpha 1
  seqNum : BitVec 32
  sendTime : BitVec 64
  messages : Bounded 1 Messages
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.pktSize
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.messages.val.length)
    ++ (Alpha.encode message.filler
    ++ (encodeUIntLE 4 message.seqNum
    ++ (encodeUIntLE 8 message.sendTime
    ++ (encodeMany Messages.encode message.messages.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (pktSize, bytes) ← decodeUIntLE 2 bytes
  let (msgCount, bytes) ← decodeUInt 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← decodeUIntLE 8 bytes
  let (messages_, bytes) ← decodeMany Messages.decode msgCount.toNat bytes
  if fits_messages : messages_.length < 256 ^ 1 then
    pure ({ pktSize, filler, seqNum, sendTime, messages := ⟨messages_, fits_messages⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 21904333211146 := by
  have bound_messages := message.messages.length_lt
  have bound_messages_items := encodeMany_length_le Messages.encode 85899345926 Messages.encode_length_le message.messages.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Messages.encode Messages.decode Messages.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.messages.length_lt]
  rfl

end Packet

end Omi.LmeLmeselectDailysummariessnapshotLmesourceV418
