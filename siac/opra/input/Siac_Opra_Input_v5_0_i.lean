import Wire

/-!
# The Securities Industry Automation Corporation Input v5.0.i

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.SiacOpraInputObiV50I

/-- Participant Id: one byte code -/
def ParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x47, 0x48, 0x49, 0x4A, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x5A]

inductive ParticipantId where
  | amex -- AMEX
  | box -- BOX
  | cboe -- CBOE
  | emerald -- EMERALD
  | edgx -- EDGX
  | mx2 -- MX2
  | gemx -- GEMX
  | ise -- ISE
  | mrx -- MRX
  | miax -- MIAX
  | nyse -- NYSE
  | opra -- OPRA
  | pearl -- PEARL
  | nasd -- NASD
  | sphr -- SPHR
  | bx -- BX
  | memx -- MEMX
  | iex -- IEX
  | c2 -- C2
  | phlx -- PHLX
  | bats -- BATS
  | unlisted (byte : { byte : UInt8 // byte ∉ ParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ParticipantId

def toByte : ParticipantId → UInt8
  | .amex => 0x41
  | .box => 0x42
  | .cboe => 0x43
  | .emerald => 0x44
  | .edgx => 0x45
  | .mx2 => 0x47
  | .gemx => 0x48
  | .ise => 0x49
  | .mrx => 0x4A
  | .miax => 0x4D
  | .nyse => 0x4E
  | .opra => 0x4F
  | .pearl => 0x50
  | .nasd => 0x51
  | .sphr => 0x53
  | .bx => 0x54
  | .memx => 0x55
  | .iex => 0x56
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
  else if byte = 0x47 then .mx2
  else if byte = 0x48 then .gemx
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .mrx
  else if byte = 0x4D then .miax
  else if byte = 0x4E then .nyse
  else if byte = 0x4F then .opra
  else if byte = 0x50 then .pearl
  else if byte = 0x51 then .nasd
  else if byte = 0x53 then .sphr
  else if byte = 0x54 then .bx
  else if byte = 0x55 then .memx
  else if byte = 0x56 then .iex
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
  | mx2 => decide
  | gemx => decide
  | ise => decide
  | mrx => decide
  | miax => decide
  | nyse => decide
  | opra => decide
  | pearl => decide
  | nasd => decide
  | sphr => decide
  | bx => decide
  | memx => decide
  | iex => decide
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

/-- Expiration Month: one byte code -/
def ExpirationMonth.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58]

inductive ExpirationMonth where
  | callJanuary -- Call January
  | callFebruary -- Call February
  | callMarch -- Call March
  | callApril -- Call April
  | callMay -- Call May
  | callJune -- Call June
  | callJuly -- Call July
  | callAugust -- Call August
  | callSeptember -- Call September
  | callOctober -- Call October
  | callNovember -- Call November
  | callDecember -- Call December
  | putJanuary -- Put January
  | putFebruary -- Put February
  | putMarch -- Put March
  | putApril -- Put April
  | putMay -- Put May
  | putJune -- Put June
  | putJuly -- Put July
  | putAugust -- Put August
  | putSeptember -- Put September
  | putOctober -- Put October
  | putNovember -- Put November
  | putDecember -- Put December
  | unlisted (byte : { byte : UInt8 // byte ∉ ExpirationMonth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExpirationMonth

def toByte : ExpirationMonth → UInt8
  | .callJanuary => 0x41
  | .callFebruary => 0x42
  | .callMarch => 0x43
  | .callApril => 0x44
  | .callMay => 0x45
  | .callJune => 0x46
  | .callJuly => 0x47
  | .callAugust => 0x48
  | .callSeptember => 0x49
  | .callOctober => 0x4A
  | .callNovember => 0x4B
  | .callDecember => 0x4C
  | .putJanuary => 0x4D
  | .putFebruary => 0x4E
  | .putMarch => 0x4F
  | .putApril => 0x50
  | .putMay => 0x51
  | .putJune => 0x52
  | .putJuly => 0x53
  | .putAugust => 0x54
  | .putSeptember => 0x55
  | .putOctober => 0x56
  | .putNovember => 0x57
  | .putDecember => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExpirationMonth :=
  if byte = 0x41 then .callJanuary
  else if byte = 0x42 then .callFebruary
  else if byte = 0x43 then .callMarch
  else if byte = 0x44 then .callApril
  else if byte = 0x45 then .callMay
  else if byte = 0x46 then .callJune
  else if byte = 0x47 then .callJuly
  else if byte = 0x48 then .callAugust
  else if byte = 0x49 then .callSeptember
  else if byte = 0x4A then .callOctober
  else if byte = 0x4B then .callNovember
  else if byte = 0x4C then .callDecember
  else if byte = 0x4D then .putJanuary
  else if byte = 0x4E then .putFebruary
  else if byte = 0x4F then .putMarch
  else if byte = 0x50 then .putApril
  else if byte = 0x51 then .putMay
  else if byte = 0x52 then .putJune
  else if byte = 0x53 then .putJuly
  else if byte = 0x54 then .putAugust
  else if byte = 0x55 then .putSeptember
  else if byte = 0x56 then .putOctober
  else if byte = 0x57 then .putNovember
  else .putDecember

def ofByte (byte : UInt8) : ExpirationMonth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExpirationMonth) : ofByte value.toByte = value := by
  cases value with
  | callJanuary => decide
  | callFebruary => decide
  | callMarch => decide
  | callApril => decide
  | callMay => decide
  | callJune => decide
  | callJuly => decide
  | callAugust => decide
  | callSeptember => decide
  | callOctober => decide
  | callNovember => decide
  | callDecember => decide
  | putJanuary => decide
  | putFebruary => decide
  | putMarch => decide
  | putApril => decide
  | putMay => decide
  | putJune => decide
  | putJuly => decide
  | putAugust => decide
  | putSeptember => decide
  | putOctober => decide
  | putNovember => decide
  | putDecember => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExpirationMonth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExpirationMonth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExpirationMonth) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExpirationMonth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExpirationMonth

/-- Strike Price Denominator Code: one byte code -/
def StrikePriceDenominatorCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x49]

inductive StrikePriceDenominatorCode where
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | noFraction -- No Fraction
  | unlisted (byte : { byte : UInt8 // byte ∉ StrikePriceDenominatorCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrikePriceDenominatorCode

def toByte : StrikePriceDenominatorCode → UInt8
  | .ten => 0x41
  | .hundred => 0x42
  | .thousand => 0x43
  | .tenThousand => 0x44
  | .hundredThousand => 0x45
  | .noFraction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrikePriceDenominatorCode :=
  if byte = 0x41 then .ten
  else if byte = 0x42 then .hundred
  else if byte = 0x43 then .thousand
  else if byte = 0x44 then .tenThousand
  else if byte = 0x45 then .hundredThousand
  else .noFraction

def ofByte (byte : UInt8) : StrikePriceDenominatorCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrikePriceDenominatorCode) : ofByte value.toByte = value := by
  cases value with
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | noFraction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrikePriceDenominatorCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrikePriceDenominatorCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrikePriceDenominatorCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StrikePriceDenominatorCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrikePriceDenominatorCode

/-- Premium Price Denominator Code: one byte code -/
def PremiumPriceDenominatorCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x49]

inductive PremiumPriceDenominatorCode where
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | noFraction -- No Fraction
  | unlisted (byte : { byte : UInt8 // byte ∉ PremiumPriceDenominatorCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PremiumPriceDenominatorCode

def toByte : PremiumPriceDenominatorCode → UInt8
  | .ten => 0x41
  | .hundred => 0x42
  | .thousand => 0x43
  | .tenThousand => 0x44
  | .hundredThousand => 0x45
  | .million => 0x46
  | .tenMillion => 0x47
  | .noFraction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PremiumPriceDenominatorCode :=
  if byte = 0x41 then .ten
  else if byte = 0x42 then .hundred
  else if byte = 0x43 then .thousand
  else if byte = 0x44 then .tenThousand
  else if byte = 0x45 then .hundredThousand
  else if byte = 0x46 then .million
  else if byte = 0x47 then .tenMillion
  else .noFraction

def ofByte (byte : UInt8) : PremiumPriceDenominatorCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PremiumPriceDenominatorCode) : ofByte value.toByte = value := by
  cases value with
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | noFraction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PremiumPriceDenominatorCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PremiumPriceDenominatorCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PremiumPriceDenominatorCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PremiumPriceDenominatorCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PremiumPriceDenominatorCode

/-- Underlying Price Denominator Code: one byte code -/
def UnderlyingPriceDenominatorCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49]

inductive UnderlyingPriceDenominatorCode where
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | noFraction -- No Fraction
  | unlisted (byte : { byte : UInt8 // byte ∉ UnderlyingPriceDenominatorCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UnderlyingPriceDenominatorCode

def toByte : UnderlyingPriceDenominatorCode → UInt8
  | .ten => 0x41
  | .hundred => 0x42
  | .thousand => 0x43
  | .tenThousand => 0x44
  | .hundredThousand => 0x45
  | .million => 0x46
  | .tenMillion => 0x47
  | .hundredMillion => 0x48
  | .noFraction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UnderlyingPriceDenominatorCode :=
  if byte = 0x41 then .ten
  else if byte = 0x42 then .hundred
  else if byte = 0x43 then .thousand
  else if byte = 0x44 then .tenThousand
  else if byte = 0x45 then .hundredThousand
  else if byte = 0x46 then .million
  else if byte = 0x47 then .tenMillion
  else if byte = 0x48 then .hundredMillion
  else .noFraction

def ofByte (byte : UInt8) : UnderlyingPriceDenominatorCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UnderlyingPriceDenominatorCode) : ofByte value.toByte = value := by
  cases value with
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | noFraction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UnderlyingPriceDenominatorCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UnderlyingPriceDenominatorCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UnderlyingPriceDenominatorCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : UnderlyingPriceDenominatorCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UnderlyingPriceDenominatorCode

/-- Index Value Denominator Code: one byte code -/
def IndexValueDenominatorCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x49]

inductive IndexValueDenominatorCode where
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | noFraction -- No Fraction
  | unlisted (byte : { byte : UInt8 // byte ∉ IndexValueDenominatorCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IndexValueDenominatorCode

def toByte : IndexValueDenominatorCode → UInt8
  | .ten => 0x41
  | .hundred => 0x42
  | .thousand => 0x43
  | .tenThousand => 0x44
  | .hundredThousand => 0x45
  | .million => 0x46
  | .tenMillion => 0x47
  | .noFraction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IndexValueDenominatorCode :=
  if byte = 0x41 then .ten
  else if byte = 0x42 then .hundred
  else if byte = 0x43 then .thousand
  else if byte = 0x44 then .tenThousand
  else if byte = 0x45 then .hundredThousand
  else if byte = 0x46 then .million
  else if byte = 0x47 then .tenMillion
  else .noFraction

def ofByte (byte : UInt8) : IndexValueDenominatorCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IndexValueDenominatorCode) : ofByte value.toByte = value := by
  cases value with
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | noFraction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IndexValueDenominatorCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IndexValueDenominatorCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IndexValueDenominatorCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IndexValueDenominatorCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IndexValueDenominatorCode

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

/-- Expiration Block: 3 bytes -/
structure ExpirationBlock where
  expirationMonth : ExpirationMonth
  expirationDay : BitVec 8
  expirationYear : BitVec 8
  deriving DecidableEq, Repr

namespace ExpirationBlock

def encode (message : ExpirationBlock) : List UInt8 :=
  ExpirationMonth.encode message.expirationMonth
    ++ (encodeUInt 1 message.expirationDay
    ++ (encodeUInt 1 message.expirationYear))

def decode (bytes : List UInt8) : Option (ExpirationBlock × List UInt8) := do
  let (expirationMonth, bytes) ← ExpirationMonth.decode bytes
  let (expirationDay, bytes) ← decodeUInt 1 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  pure ({ expirationMonth, expirationDay, expirationYear }, bytes)

@[simp] theorem encode_length (message : ExpirationBlock) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, ExpirationMonth.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ExpirationBlock) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExpirationBlock) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExpirationMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExpirationBlock

/-- Equity And Index Last Sale Message: 36 bytes -/
structure EquityAndIndexLastSaleMessage where
  sessionIndicator : BitVec 8
  participantReferenceNumber : BitVec 32
  securitySymbol : Alpha 5
  reserved1 : Alpha 1
  expirationBlock : ExpirationBlock
  strikePriceDenominatorCode : StrikePriceDenominatorCode
  strikePrice : BitVec 32
  volume : BitVec 32
  premiumPriceDenominatorCode : PremiumPriceDenominatorCode
  premiumPrice : BitVec 32
  tradeIdentifier : BitVec 32
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace EquityAndIndexLastSaleMessage

def encode (message : EquityAndIndexLastSaleMessage) : List UInt8 :=
  encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.reserved1
    ++ (ExpirationBlock.encode message.expirationBlock
    ++ (StrikePriceDenominatorCode.encode message.strikePriceDenominatorCode
    ++ (encodeUInt 4 message.strikePrice
    ++ (encodeUInt 4 message.volume
    ++ (PremiumPriceDenominatorCode.encode message.premiumPriceDenominatorCode
    ++ (encodeUInt 4 message.premiumPrice
    ++ (encodeUInt 4 message.tradeIdentifier
    ++ (Alpha.encode message.reserved4)))))))))))

def decode (bytes : List UInt8) : Option (EquityAndIndexLastSaleMessage × List UInt8) := do
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (expirationBlock, bytes) ← ExpirationBlock.decode bytes
  let (strikePriceDenominatorCode, bytes) ← StrikePriceDenominatorCode.decode bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (premiumPriceDenominatorCode, bytes) ← PremiumPriceDenominatorCode.decode bytes
  let (premiumPrice, bytes) ← decodeUInt 4 bytes
  let (tradeIdentifier, bytes) ← decodeUInt 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ sessionIndicator, participantReferenceNumber, securitySymbol, reserved1, expirationBlock, strikePriceDenominatorCode, strikePrice, volume, premiumPriceDenominatorCode, premiumPrice, tradeIdentifier, reserved4 }, bytes)

@[simp] theorem encode_length (message : EquityAndIndexLastSaleMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length]

theorem encode_length_pos (message : EquityAndIndexLastSaleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquityAndIndexLastSaleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpirationBlock.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PremiumPriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EquityAndIndexLastSaleMessage

/-- Any Equity And Index Last Sale Message Payload, selected by Equity And Index Last Sale Message Type -/
inductive EquityAndIndexLastSaleMessagePayload where
  | equityAndIndexLastSaleMessage (message : EquityAndIndexLastSaleMessage) -- "A" 0x41
  | equityAndIndexLastSaleMessage66 (message : EquityAndIndexLastSaleMessage) -- "B" 0x42
  | equityAndIndexLastSaleMessage67 (message : EquityAndIndexLastSaleMessage) -- "C" 0x43
  | equityAndIndexLastSaleMessage68 (message : EquityAndIndexLastSaleMessage) -- "D" 0x44
  | equityAndIndexLastSaleMessage69 (message : EquityAndIndexLastSaleMessage) -- "E" 0x45
  | equityAndIndexLastSaleMessage70 (message : EquityAndIndexLastSaleMessage) -- "F" 0x46
  | equityAndIndexLastSaleMessage71 (message : EquityAndIndexLastSaleMessage) -- "G" 0x47
  | equityAndIndexLastSaleMessage72 (message : EquityAndIndexLastSaleMessage) -- "H" 0x48
  | equityAndIndexLastSaleMessage73 (message : EquityAndIndexLastSaleMessage) -- "I" 0x49
  | equityAndIndexLastSaleMessage74 (message : EquityAndIndexLastSaleMessage) -- "J" 0x4A
  | equityAndIndexLastSaleMessage83 (message : EquityAndIndexLastSaleMessage) -- "S" 0x53
  | equityAndIndexLastSaleMessage97 (message : EquityAndIndexLastSaleMessage) -- "a" 0x61
  | equityAndIndexLastSaleMessage98 (message : EquityAndIndexLastSaleMessage) -- "b" 0x62
  | equityAndIndexLastSaleMessage99 (message : EquityAndIndexLastSaleMessage) -- "c" 0x63
  | equityAndIndexLastSaleMessage100 (message : EquityAndIndexLastSaleMessage) -- "d" 0x64
  | equityAndIndexLastSaleMessage101 (message : EquityAndIndexLastSaleMessage) -- "e" 0x65
  | equityAndIndexLastSaleMessage102 (message : EquityAndIndexLastSaleMessage) -- "f" 0x66
  | equityAndIndexLastSaleMessage103 (message : EquityAndIndexLastSaleMessage) -- "g" 0x67
  | equityAndIndexLastSaleMessage104 (message : EquityAndIndexLastSaleMessage) -- "h" 0x68
  | equityAndIndexLastSaleMessage105 (message : EquityAndIndexLastSaleMessage) -- "i" 0x69
  | equityAndIndexLastSaleMessage106 (message : EquityAndIndexLastSaleMessage) -- "j" 0x6A
  | equityAndIndexLastSaleMessage107 (message : EquityAndIndexLastSaleMessage) -- "k" 0x6B
  | equityAndIndexLastSaleMessage108 (message : EquityAndIndexLastSaleMessage) -- "l" 0x6C
  | equityAndIndexLastSaleMessage109 (message : EquityAndIndexLastSaleMessage) -- "m" 0x6D
  | equityAndIndexLastSaleMessage110 (message : EquityAndIndexLastSaleMessage) -- "n" 0x6E
  | equityAndIndexLastSaleMessage111 (message : EquityAndIndexLastSaleMessage) -- "o" 0x6F
  | equityAndIndexLastSaleMessage112 (message : EquityAndIndexLastSaleMessage) -- "p" 0x70
  | equityAndIndexLastSaleMessage113 (message : EquityAndIndexLastSaleMessage) -- "q" 0x71
  | equityAndIndexLastSaleMessage114 (message : EquityAndIndexLastSaleMessage) -- "r" 0x72
  | equityAndIndexLastSaleMessage115 (message : EquityAndIndexLastSaleMessage) -- "s" 0x73
  | equityAndIndexLastSaleMessage116 (message : EquityAndIndexLastSaleMessage) -- "t" 0x74
  | equityAndIndexLastSaleMessage117 (message : EquityAndIndexLastSaleMessage) -- "u" 0x75
  | equityAndIndexLastSaleMessage118 (message : EquityAndIndexLastSaleMessage) -- "v" 0x76
  deriving DecidableEq, Repr

namespace EquityAndIndexLastSaleMessagePayload

/-- The Equity And Index Last Sale Message Type each message is sent under -/
def tag : EquityAndIndexLastSaleMessagePayload → BitVec 8
  | .equityAndIndexLastSaleMessage _ => 65
  | .equityAndIndexLastSaleMessage66 _ => 66
  | .equityAndIndexLastSaleMessage67 _ => 67
  | .equityAndIndexLastSaleMessage68 _ => 68
  | .equityAndIndexLastSaleMessage69 _ => 69
  | .equityAndIndexLastSaleMessage70 _ => 70
  | .equityAndIndexLastSaleMessage71 _ => 71
  | .equityAndIndexLastSaleMessage72 _ => 72
  | .equityAndIndexLastSaleMessage73 _ => 73
  | .equityAndIndexLastSaleMessage74 _ => 74
  | .equityAndIndexLastSaleMessage83 _ => 83
  | .equityAndIndexLastSaleMessage97 _ => 97
  | .equityAndIndexLastSaleMessage98 _ => 98
  | .equityAndIndexLastSaleMessage99 _ => 99
  | .equityAndIndexLastSaleMessage100 _ => 100
  | .equityAndIndexLastSaleMessage101 _ => 101
  | .equityAndIndexLastSaleMessage102 _ => 102
  | .equityAndIndexLastSaleMessage103 _ => 103
  | .equityAndIndexLastSaleMessage104 _ => 104
  | .equityAndIndexLastSaleMessage105 _ => 105
  | .equityAndIndexLastSaleMessage106 _ => 106
  | .equityAndIndexLastSaleMessage107 _ => 107
  | .equityAndIndexLastSaleMessage108 _ => 108
  | .equityAndIndexLastSaleMessage109 _ => 109
  | .equityAndIndexLastSaleMessage110 _ => 110
  | .equityAndIndexLastSaleMessage111 _ => 111
  | .equityAndIndexLastSaleMessage112 _ => 112
  | .equityAndIndexLastSaleMessage113 _ => 113
  | .equityAndIndexLastSaleMessage114 _ => 114
  | .equityAndIndexLastSaleMessage115 _ => 115
  | .equityAndIndexLastSaleMessage116 _ => 116
  | .equityAndIndexLastSaleMessage117 _ => 117
  | .equityAndIndexLastSaleMessage118 _ => 118

def encode : EquityAndIndexLastSaleMessagePayload → List UInt8
  | .equityAndIndexLastSaleMessage message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage66 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage67 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage68 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage69 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage70 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage71 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage72 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage73 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage74 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage83 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage97 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage98 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage99 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage100 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage101 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage102 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage103 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage104 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage105 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage106 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage107 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage108 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage109 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage110 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage111 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage112 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage113 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage114 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage115 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage116 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage117 message => EquityAndIndexLastSaleMessage.encode message
  | .equityAndIndexLastSaleMessage118 message => EquityAndIndexLastSaleMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : EquityAndIndexLastSaleMessagePayload) : (encode message).length ≤ 36 := by
  cases message with
  | equityAndIndexLastSaleMessage inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage66 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage67 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage68 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage69 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage70 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage71 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage72 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage73 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage74 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage83 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage97 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage98 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage99 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage100 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage101 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage102 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage103 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage104 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage105 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage106 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage107 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage108 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage109 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage110 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage111 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage112 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage113 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage114 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage115 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage116 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage117 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage118 inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (EquityAndIndexLastSaleMessagePayload × List UInt8) :=
  if tag = 65 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage message, rest)
  else if tag = 66 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage66 message, rest)
  else if tag = 67 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage67 message, rest)
  else if tag = 68 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage68 message, rest)
  else if tag = 69 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage69 message, rest)
  else if tag = 70 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage70 message, rest)
  else if tag = 71 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage71 message, rest)
  else if tag = 72 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage72 message, rest)
  else if tag = 73 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage73 message, rest)
  else if tag = 74 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage74 message, rest)
  else if tag = 83 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage83 message, rest)
  else if tag = 97 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage97 message, rest)
  else if tag = 98 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage98 message, rest)
  else if tag = 99 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage99 message, rest)
  else if tag = 100 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage100 message, rest)
  else if tag = 101 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage101 message, rest)
  else if tag = 102 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage102 message, rest)
  else if tag = 103 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage103 message, rest)
  else if tag = 104 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage104 message, rest)
  else if tag = 105 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage105 message, rest)
  else if tag = 106 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage106 message, rest)
  else if tag = 107 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage107 message, rest)
  else if tag = 108 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage108 message, rest)
  else if tag = 109 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage109 message, rest)
  else if tag = 110 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage110 message, rest)
  else if tag = 111 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage111 message, rest)
  else if tag = 112 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage112 message, rest)
  else if tag = 113 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage113 message, rest)
  else if tag = 114 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage114 message, rest)
  else if tag = 115 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage115 message, rest)
  else if tag = 116 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage116 message, rest)
  else if tag = 117 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage117 message, rest)
  else if tag = 118 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage118 message, rest)
  else none

@[simp] theorem decode_encode (message : EquityAndIndexLastSaleMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end EquityAndIndexLastSaleMessagePayload

/-- Equity And Index Last Sale Category -/
structure EquityAndIndexLastSaleCategory where
  equityAndIndexLastSaleMessagePayload : EquityAndIndexLastSaleMessagePayload
  deriving DecidableEq, Repr

namespace EquityAndIndexLastSaleCategory

def encode (message : EquityAndIndexLastSaleCategory) : List UInt8 :=
  encodeUInt 1 (EquityAndIndexLastSaleMessagePayload.tag message.equityAndIndexLastSaleMessagePayload)
    ++ (EquityAndIndexLastSaleMessagePayload.encode message.equityAndIndexLastSaleMessagePayload)

def decode (bytes : List UInt8) : Option (EquityAndIndexLastSaleCategory × List UInt8) := do
  let (equityAndIndexLastSaleMessageType, bytes) ← decodeUInt 1 bytes
  let (equityAndIndexLastSaleMessagePayload, bytes) ← EquityAndIndexLastSaleMessagePayload.decode equityAndIndexLastSaleMessageType bytes
  pure ({ equityAndIndexLastSaleMessagePayload }, bytes)

theorem encode_length_pos (message : EquityAndIndexLastSaleCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EquityAndIndexLastSaleCategory) : (encode message).length ≤ 37 := by
  unfold encode
  cases message.equityAndIndexLastSaleMessagePayload with
  | equityAndIndexLastSaleMessage inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage66 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage67 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage68 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage69 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage70 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage71 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage72 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage73 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage74 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage83 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage97 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage98 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage99 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage100 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage101 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage102 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage103 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage104 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage105 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage106 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage107 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage108 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage109 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage110 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage111 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage112 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage113 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage114 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage115 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage116 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage117 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega
  | equityAndIndexLastSaleMessage118 inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : EquityAndIndexLastSaleCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EquityAndIndexLastSaleMessagePayload.decode_encode, some_bind]
  rfl

end EquityAndIndexLastSaleCategory

/-- Equity And Index End Of Day Summary Message: 65 bytes -/
structure EquityAndIndexEndOfDaySummaryMessage where
  sessionIndicator : BitVec 8
  participantReferenceNumber : BitVec 32
  securitySymbol : Alpha 5
  reserved1 : Alpha 1
  expirationBlock : ExpirationBlock
  strikePriceDenominatorCode : StrikePriceDenominatorCode
  strikePrice : BitVec 32
  volume : BitVec 32
  openInterestVolume : BitVec 32
  premiumPriceDenominatorCode : PremiumPriceDenominatorCode
  openPrice : BitVec 32
  highPrice : BitVec 32
  lowPrice : BitVec 32
  lastPrice : BitVec 32
  netChange : BitVec 32
  underlyingPriceDenominatorCode : UnderlyingPriceDenominatorCode
  underlyingPrice : BitVec 64
  bidPrice : BitVec 32
  offerPrice : BitVec 32
  deriving DecidableEq, Repr

namespace EquityAndIndexEndOfDaySummaryMessage

def encode (message : EquityAndIndexEndOfDaySummaryMessage) : List UInt8 :=
  encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.reserved1
    ++ (ExpirationBlock.encode message.expirationBlock
    ++ (StrikePriceDenominatorCode.encode message.strikePriceDenominatorCode
    ++ (encodeUInt 4 message.strikePrice
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.openInterestVolume
    ++ (PremiumPriceDenominatorCode.encode message.premiumPriceDenominatorCode
    ++ (encodeUInt 4 message.openPrice
    ++ (encodeUInt 4 message.highPrice
    ++ (encodeUInt 4 message.lowPrice
    ++ (encodeUInt 4 message.lastPrice
    ++ (encodeUInt 4 message.netChange
    ++ (UnderlyingPriceDenominatorCode.encode message.underlyingPriceDenominatorCode
    ++ (encodeUInt 8 message.underlyingPrice
    ++ (encodeUInt 4 message.bidPrice
    ++ (encodeUInt 4 message.offerPrice))))))))))))))))))

def decode (bytes : List UInt8) : Option (EquityAndIndexEndOfDaySummaryMessage × List UInt8) := do
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (expirationBlock, bytes) ← ExpirationBlock.decode bytes
  let (strikePriceDenominatorCode, bytes) ← StrikePriceDenominatorCode.decode bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (openInterestVolume, bytes) ← decodeUInt 4 bytes
  let (premiumPriceDenominatorCode, bytes) ← PremiumPriceDenominatorCode.decode bytes
  let (openPrice, bytes) ← decodeUInt 4 bytes
  let (highPrice, bytes) ← decodeUInt 4 bytes
  let (lowPrice, bytes) ← decodeUInt 4 bytes
  let (lastPrice, bytes) ← decodeUInt 4 bytes
  let (netChange, bytes) ← decodeUInt 4 bytes
  let (underlyingPriceDenominatorCode, bytes) ← UnderlyingPriceDenominatorCode.decode bytes
  let (underlyingPrice, bytes) ← decodeUInt 8 bytes
  let (bidPrice, bytes) ← decodeUInt 4 bytes
  let (offerPrice, bytes) ← decodeUInt 4 bytes
  pure ({ sessionIndicator, participantReferenceNumber, securitySymbol, reserved1, expirationBlock, strikePriceDenominatorCode, strikePrice, volume, openInterestVolume, premiumPriceDenominatorCode, openPrice, highPrice, lowPrice, lastPrice, netChange, underlyingPriceDenominatorCode, underlyingPrice, bidPrice, offerPrice }, bytes)

@[simp] theorem encode_length (message : EquityAndIndexEndOfDaySummaryMessage) : (encode message).length = 65 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, UnderlyingPriceDenominatorCode.encode_length]

theorem encode_length_pos (message : EquityAndIndexEndOfDaySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquityAndIndexEndOfDaySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpirationBlock.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PremiumPriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, UnderlyingPriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EquityAndIndexEndOfDaySummaryMessage

/-- Any Equity And Index End Of Day Summary Message Payload, selected by Equity And Index End Of Day Summary Message Type -/
inductive EquityAndIndexEndOfDaySummaryMessagePayload where
  | equityAndIndexEndOfDaySummaryMessage (message : EquityAndIndexEndOfDaySummaryMessage) -- " " 0x20
  deriving DecidableEq, Repr

namespace EquityAndIndexEndOfDaySummaryMessagePayload

/-- The Equity And Index End Of Day Summary Message Type each message is sent under -/
def tag : EquityAndIndexEndOfDaySummaryMessagePayload → BitVec 8
  | .equityAndIndexEndOfDaySummaryMessage _ => 32

def encode : EquityAndIndexEndOfDaySummaryMessagePayload → List UInt8
  | .equityAndIndexEndOfDaySummaryMessage message => EquityAndIndexEndOfDaySummaryMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : EquityAndIndexEndOfDaySummaryMessagePayload) : (encode message).length ≤ 65 := by
  cases message with
  | equityAndIndexEndOfDaySummaryMessage inner =>
    simp only [encode, EquityAndIndexEndOfDaySummaryMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (EquityAndIndexEndOfDaySummaryMessagePayload × List UInt8) :=
  if tag = 32 then (EquityAndIndexEndOfDaySummaryMessage.decode bytes).map fun (message, rest) => (.equityAndIndexEndOfDaySummaryMessage message, rest)
  else none

@[simp] theorem decode_encode (message : EquityAndIndexEndOfDaySummaryMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end EquityAndIndexEndOfDaySummaryMessagePayload

/-- Equity And Index End Of Day Summary Category -/
structure EquityAndIndexEndOfDaySummaryCategory where
  equityAndIndexEndOfDaySummaryMessagePayload : EquityAndIndexEndOfDaySummaryMessagePayload
  deriving DecidableEq, Repr

namespace EquityAndIndexEndOfDaySummaryCategory

def encode (message : EquityAndIndexEndOfDaySummaryCategory) : List UInt8 :=
  encodeUInt 1 (EquityAndIndexEndOfDaySummaryMessagePayload.tag message.equityAndIndexEndOfDaySummaryMessagePayload)
    ++ (EquityAndIndexEndOfDaySummaryMessagePayload.encode message.equityAndIndexEndOfDaySummaryMessagePayload)

def decode (bytes : List UInt8) : Option (EquityAndIndexEndOfDaySummaryCategory × List UInt8) := do
  let (equityAndIndexEndOfDaySummaryMessageType, bytes) ← decodeUInt 1 bytes
  let (equityAndIndexEndOfDaySummaryMessagePayload, bytes) ← EquityAndIndexEndOfDaySummaryMessagePayload.decode equityAndIndexEndOfDaySummaryMessageType bytes
  pure ({ equityAndIndexEndOfDaySummaryMessagePayload }, bytes)

theorem encode_length_pos (message : EquityAndIndexEndOfDaySummaryCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EquityAndIndexEndOfDaySummaryCategory) : (encode message).length ≤ 66 := by
  unfold encode
  cases message.equityAndIndexEndOfDaySummaryMessagePayload with
  | equityAndIndexEndOfDaySummaryMessage inner =>
    simp only [EquityAndIndexEndOfDaySummaryMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexEndOfDaySummaryMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : EquityAndIndexEndOfDaySummaryCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EquityAndIndexEndOfDaySummaryMessagePayload.decode_encode, some_bind]
  rfl

end EquityAndIndexEndOfDaySummaryCategory

/-- Long Equity And Index Quote Message: 36 bytes -/
structure LongEquityAndIndexQuoteMessage where
  sessionIndicator : BitVec 8
  participantReferenceNumber : BitVec 32
  securitySymbol : Alpha 5
  reserved1 : Alpha 1
  expirationBlock : ExpirationBlock
  strikePriceDenominatorCode : StrikePriceDenominatorCode
  strikePrice : BitVec 32
  premiumPriceDenominatorCode : PremiumPriceDenominatorCode
  bidPrice : BitVec 32
  bidSize : BitVec 32
  offerPrice : BitVec 32
  offerSize : BitVec 32
  deriving DecidableEq, Repr

namespace LongEquityAndIndexQuoteMessage

def encode (message : LongEquityAndIndexQuoteMessage) : List UInt8 :=
  encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.reserved1
    ++ (ExpirationBlock.encode message.expirationBlock
    ++ (StrikePriceDenominatorCode.encode message.strikePriceDenominatorCode
    ++ (encodeUInt 4 message.strikePrice
    ++ (PremiumPriceDenominatorCode.encode message.premiumPriceDenominatorCode
    ++ (encodeUInt 4 message.bidPrice
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 4 message.offerPrice
    ++ (encodeUInt 4 message.offerSize)))))))))))

def decode (bytes : List UInt8) : Option (LongEquityAndIndexQuoteMessage × List UInt8) := do
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (expirationBlock, bytes) ← ExpirationBlock.decode bytes
  let (strikePriceDenominatorCode, bytes) ← StrikePriceDenominatorCode.decode bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (premiumPriceDenominatorCode, bytes) ← PremiumPriceDenominatorCode.decode bytes
  let (bidPrice, bytes) ← decodeUInt 4 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (offerPrice, bytes) ← decodeUInt 4 bytes
  let (offerSize, bytes) ← decodeUInt 4 bytes
  pure ({ sessionIndicator, participantReferenceNumber, securitySymbol, reserved1, expirationBlock, strikePriceDenominatorCode, strikePrice, premiumPriceDenominatorCode, bidPrice, bidSize, offerPrice, offerSize }, bytes)

@[simp] theorem encode_length (message : LongEquityAndIndexQuoteMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length]

theorem encode_length_pos (message : LongEquityAndIndexQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongEquityAndIndexQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpirationBlock.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PremiumPriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LongEquityAndIndexQuoteMessage

/-- Any Long Equity And Index Quote Message Payload, selected by Long Equity And Index Quote Message Type -/
inductive LongEquityAndIndexQuoteMessagePayload where
  | longEquityAndIndexQuoteMessage (message : LongEquityAndIndexQuoteMessage) -- " " 0x20
  | longEquityAndIndexQuoteMessage70 (message : LongEquityAndIndexQuoteMessage) -- "F" 0x46
  | longEquityAndIndexQuoteMessage73 (message : LongEquityAndIndexQuoteMessage) -- "I" 0x49
  | longEquityAndIndexQuoteMessage82 (message : LongEquityAndIndexQuoteMessage) -- "R" 0x52
  | longEquityAndIndexQuoteMessage84 (message : LongEquityAndIndexQuoteMessage) -- "T" 0x54
  | longEquityAndIndexQuoteMessage65 (message : LongEquityAndIndexQuoteMessage) -- "A" 0x41
  | longEquityAndIndexQuoteMessage66 (message : LongEquityAndIndexQuoteMessage) -- "B" 0x42
  | longEquityAndIndexQuoteMessage79 (message : LongEquityAndIndexQuoteMessage) -- "O" 0x4F
  | longEquityAndIndexQuoteMessage67 (message : LongEquityAndIndexQuoteMessage) -- "C" 0x43
  | longEquityAndIndexQuoteMessage88 (message : LongEquityAndIndexQuoteMessage) -- "X" 0x58
  | longEquityAndIndexQuoteMessage89 (message : LongEquityAndIndexQuoteMessage) -- "Y" 0x59
  deriving DecidableEq, Repr

namespace LongEquityAndIndexQuoteMessagePayload

/-- The Long Equity And Index Quote Message Type each message is sent under -/
def tag : LongEquityAndIndexQuoteMessagePayload → BitVec 8
  | .longEquityAndIndexQuoteMessage _ => 32
  | .longEquityAndIndexQuoteMessage70 _ => 70
  | .longEquityAndIndexQuoteMessage73 _ => 73
  | .longEquityAndIndexQuoteMessage82 _ => 82
  | .longEquityAndIndexQuoteMessage84 _ => 84
  | .longEquityAndIndexQuoteMessage65 _ => 65
  | .longEquityAndIndexQuoteMessage66 _ => 66
  | .longEquityAndIndexQuoteMessage79 _ => 79
  | .longEquityAndIndexQuoteMessage67 _ => 67
  | .longEquityAndIndexQuoteMessage88 _ => 88
  | .longEquityAndIndexQuoteMessage89 _ => 89

def encode : LongEquityAndIndexQuoteMessagePayload → List UInt8
  | .longEquityAndIndexQuoteMessage message => LongEquityAndIndexQuoteMessage.encode message
  | .longEquityAndIndexQuoteMessage70 message => LongEquityAndIndexQuoteMessage.encode message
  | .longEquityAndIndexQuoteMessage73 message => LongEquityAndIndexQuoteMessage.encode message
  | .longEquityAndIndexQuoteMessage82 message => LongEquityAndIndexQuoteMessage.encode message
  | .longEquityAndIndexQuoteMessage84 message => LongEquityAndIndexQuoteMessage.encode message
  | .longEquityAndIndexQuoteMessage65 message => LongEquityAndIndexQuoteMessage.encode message
  | .longEquityAndIndexQuoteMessage66 message => LongEquityAndIndexQuoteMessage.encode message
  | .longEquityAndIndexQuoteMessage79 message => LongEquityAndIndexQuoteMessage.encode message
  | .longEquityAndIndexQuoteMessage67 message => LongEquityAndIndexQuoteMessage.encode message
  | .longEquityAndIndexQuoteMessage88 message => LongEquityAndIndexQuoteMessage.encode message
  | .longEquityAndIndexQuoteMessage89 message => LongEquityAndIndexQuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : LongEquityAndIndexQuoteMessagePayload) : (encode message).length ≤ 36 := by
  cases message with
  | longEquityAndIndexQuoteMessage inner =>
    simp only [encode, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage70 inner =>
    simp only [encode, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage73 inner =>
    simp only [encode, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage82 inner =>
    simp only [encode, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage84 inner =>
    simp only [encode, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage65 inner =>
    simp only [encode, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage66 inner =>
    simp only [encode, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage79 inner =>
    simp only [encode, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage67 inner =>
    simp only [encode, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage88 inner =>
    simp only [encode, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage89 inner =>
    simp only [encode, LongEquityAndIndexQuoteMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (LongEquityAndIndexQuoteMessagePayload × List UInt8) :=
  if tag = 32 then (LongEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteMessage message, rest)
  else if tag = 70 then (LongEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteMessage70 message, rest)
  else if tag = 73 then (LongEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteMessage73 message, rest)
  else if tag = 82 then (LongEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteMessage82 message, rest)
  else if tag = 84 then (LongEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteMessage84 message, rest)
  else if tag = 65 then (LongEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteMessage65 message, rest)
  else if tag = 66 then (LongEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteMessage66 message, rest)
  else if tag = 79 then (LongEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteMessage79 message, rest)
  else if tag = 67 then (LongEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteMessage67 message, rest)
  else if tag = 88 then (LongEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteMessage88 message, rest)
  else if tag = 89 then (LongEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteMessage89 message, rest)
  else none

@[simp] theorem decode_encode (message : LongEquityAndIndexQuoteMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end LongEquityAndIndexQuoteMessagePayload

/-- Long Equity And Index Quote Category -/
structure LongEquityAndIndexQuoteCategory where
  longEquityAndIndexQuoteMessagePayload : LongEquityAndIndexQuoteMessagePayload
  deriving DecidableEq, Repr

namespace LongEquityAndIndexQuoteCategory

def encode (message : LongEquityAndIndexQuoteCategory) : List UInt8 :=
  encodeUInt 1 (LongEquityAndIndexQuoteMessagePayload.tag message.longEquityAndIndexQuoteMessagePayload)
    ++ (LongEquityAndIndexQuoteMessagePayload.encode message.longEquityAndIndexQuoteMessagePayload)

def decode (bytes : List UInt8) : Option (LongEquityAndIndexQuoteCategory × List UInt8) := do
  let (longEquityAndIndexQuoteMessageType, bytes) ← decodeUInt 1 bytes
  let (longEquityAndIndexQuoteMessagePayload, bytes) ← LongEquityAndIndexQuoteMessagePayload.decode longEquityAndIndexQuoteMessageType bytes
  pure ({ longEquityAndIndexQuoteMessagePayload }, bytes)

theorem encode_length_pos (message : LongEquityAndIndexQuoteCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongEquityAndIndexQuoteCategory) : (encode message).length ≤ 37 := by
  unfold encode
  cases message.longEquityAndIndexQuoteMessagePayload with
  | longEquityAndIndexQuoteMessage inner =>
    simp only [LongEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage70 inner =>
    simp only [LongEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage73 inner =>
    simp only [LongEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage82 inner =>
    simp only [LongEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage84 inner =>
    simp only [LongEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage65 inner =>
    simp only [LongEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage66 inner =>
    simp only [LongEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage79 inner =>
    simp only [LongEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage67 inner =>
    simp only [LongEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage88 inner =>
    simp only [LongEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, LongEquityAndIndexQuoteMessage.encode_length]
    omega
  | longEquityAndIndexQuoteMessage89 inner =>
    simp only [LongEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, LongEquityAndIndexQuoteMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : LongEquityAndIndexQuoteCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [LongEquityAndIndexQuoteMessagePayload.decode_encode, some_bind]
  rfl

end LongEquityAndIndexQuoteCategory

/-- Short Equity And Index Quote Message: 22 bytes -/
structure ShortEquityAndIndexQuoteMessage where
  sessionIndicator : BitVec 8
  participantReferenceNumber : BitVec 32
  securitySymbolShort : Alpha 4
  expirationBlock : ExpirationBlock
  strikePriceShort : BitVec 16
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  offerPriceShort : BitVec 16
  offerSizeShort : BitVec 16
  deriving DecidableEq, Repr

namespace ShortEquityAndIndexQuoteMessage

def encode (message : ShortEquityAndIndexQuoteMessage) : List UInt8 :=
  encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbolShort
    ++ (ExpirationBlock.encode message.expirationBlock
    ++ (encodeUInt 2 message.strikePriceShort
    ++ (encodeUInt 2 message.bidPriceShort
    ++ (encodeUInt 2 message.bidSizeShort
    ++ (encodeUInt 2 message.offerPriceShort
    ++ (encodeUInt 2 message.offerSizeShort))))))))

def decode (bytes : List UInt8) : Option (ShortEquityAndIndexQuoteMessage × List UInt8) := do
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (securitySymbolShort, bytes) ← Alpha.decode 4 bytes
  let (expirationBlock, bytes) ← ExpirationBlock.decode bytes
  let (strikePriceShort, bytes) ← decodeUInt 2 bytes
  let (bidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bidSizeShort, bytes) ← decodeUInt 2 bytes
  let (offerPriceShort, bytes) ← decodeUInt 2 bytes
  let (offerSizeShort, bytes) ← decodeUInt 2 bytes
  pure ({ sessionIndicator, participantReferenceNumber, securitySymbolShort, expirationBlock, strikePriceShort, bidPriceShort, bidSizeShort, offerPriceShort, offerSizeShort }, bytes)

@[simp] theorem encode_length (message : ShortEquityAndIndexQuoteMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length]

theorem encode_length_pos (message : ShortEquityAndIndexQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortEquityAndIndexQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpirationBlock.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ShortEquityAndIndexQuoteMessage

/-- Any Short Equity And Index Quote Message Payload, selected by Short Equity And Index Quote Message Type -/
inductive ShortEquityAndIndexQuoteMessagePayload where
  | shortEquityAndIndexQuoteMessage (message : ShortEquityAndIndexQuoteMessage) -- " " 0x20
  | shortEquityAndIndexQuoteMessage70 (message : ShortEquityAndIndexQuoteMessage) -- "F" 0x46
  | shortEquityAndIndexQuoteMessage73 (message : ShortEquityAndIndexQuoteMessage) -- "I" 0x49
  | shortEquityAndIndexQuoteMessage82 (message : ShortEquityAndIndexQuoteMessage) -- "R" 0x52
  | shortEquityAndIndexQuoteMessage84 (message : ShortEquityAndIndexQuoteMessage) -- "T" 0x54
  | shortEquityAndIndexQuoteMessage65 (message : ShortEquityAndIndexQuoteMessage) -- "A" 0x41
  | shortEquityAndIndexQuoteMessage66 (message : ShortEquityAndIndexQuoteMessage) -- "B" 0x42
  | shortEquityAndIndexQuoteMessage79 (message : ShortEquityAndIndexQuoteMessage) -- "O" 0x4F
  | shortEquityAndIndexQuoteMessage67 (message : ShortEquityAndIndexQuoteMessage) -- "C" 0x43
  | shortEquityAndIndexQuoteMessage88 (message : ShortEquityAndIndexQuoteMessage) -- "X" 0x58
  | shortEquityAndIndexQuoteMessage89 (message : ShortEquityAndIndexQuoteMessage) -- "Y" 0x59
  deriving DecidableEq, Repr

namespace ShortEquityAndIndexQuoteMessagePayload

/-- The Short Equity And Index Quote Message Type each message is sent under -/
def tag : ShortEquityAndIndexQuoteMessagePayload → BitVec 8
  | .shortEquityAndIndexQuoteMessage _ => 32
  | .shortEquityAndIndexQuoteMessage70 _ => 70
  | .shortEquityAndIndexQuoteMessage73 _ => 73
  | .shortEquityAndIndexQuoteMessage82 _ => 82
  | .shortEquityAndIndexQuoteMessage84 _ => 84
  | .shortEquityAndIndexQuoteMessage65 _ => 65
  | .shortEquityAndIndexQuoteMessage66 _ => 66
  | .shortEquityAndIndexQuoteMessage79 _ => 79
  | .shortEquityAndIndexQuoteMessage67 _ => 67
  | .shortEquityAndIndexQuoteMessage88 _ => 88
  | .shortEquityAndIndexQuoteMessage89 _ => 89

def encode : ShortEquityAndIndexQuoteMessagePayload → List UInt8
  | .shortEquityAndIndexQuoteMessage message => ShortEquityAndIndexQuoteMessage.encode message
  | .shortEquityAndIndexQuoteMessage70 message => ShortEquityAndIndexQuoteMessage.encode message
  | .shortEquityAndIndexQuoteMessage73 message => ShortEquityAndIndexQuoteMessage.encode message
  | .shortEquityAndIndexQuoteMessage82 message => ShortEquityAndIndexQuoteMessage.encode message
  | .shortEquityAndIndexQuoteMessage84 message => ShortEquityAndIndexQuoteMessage.encode message
  | .shortEquityAndIndexQuoteMessage65 message => ShortEquityAndIndexQuoteMessage.encode message
  | .shortEquityAndIndexQuoteMessage66 message => ShortEquityAndIndexQuoteMessage.encode message
  | .shortEquityAndIndexQuoteMessage79 message => ShortEquityAndIndexQuoteMessage.encode message
  | .shortEquityAndIndexQuoteMessage67 message => ShortEquityAndIndexQuoteMessage.encode message
  | .shortEquityAndIndexQuoteMessage88 message => ShortEquityAndIndexQuoteMessage.encode message
  | .shortEquityAndIndexQuoteMessage89 message => ShortEquityAndIndexQuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ShortEquityAndIndexQuoteMessagePayload) : (encode message).length ≤ 22 := by
  cases message with
  | shortEquityAndIndexQuoteMessage inner =>
    simp only [encode, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage70 inner =>
    simp only [encode, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage73 inner =>
    simp only [encode, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage82 inner =>
    simp only [encode, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage84 inner =>
    simp only [encode, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage65 inner =>
    simp only [encode, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage66 inner =>
    simp only [encode, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage79 inner =>
    simp only [encode, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage67 inner =>
    simp only [encode, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage88 inner =>
    simp only [encode, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage89 inner =>
    simp only [encode, ShortEquityAndIndexQuoteMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ShortEquityAndIndexQuoteMessagePayload × List UInt8) :=
  if tag = 32 then (ShortEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteMessage message, rest)
  else if tag = 70 then (ShortEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteMessage70 message, rest)
  else if tag = 73 then (ShortEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteMessage73 message, rest)
  else if tag = 82 then (ShortEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteMessage82 message, rest)
  else if tag = 84 then (ShortEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteMessage84 message, rest)
  else if tag = 65 then (ShortEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteMessage65 message, rest)
  else if tag = 66 then (ShortEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteMessage66 message, rest)
  else if tag = 79 then (ShortEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteMessage79 message, rest)
  else if tag = 67 then (ShortEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteMessage67 message, rest)
  else if tag = 88 then (ShortEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteMessage88 message, rest)
  else if tag = 89 then (ShortEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteMessage89 message, rest)
  else none

@[simp] theorem decode_encode (message : ShortEquityAndIndexQuoteMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ShortEquityAndIndexQuoteMessagePayload

/-- Short Equity And Index Quote Category -/
structure ShortEquityAndIndexQuoteCategory where
  shortEquityAndIndexQuoteMessagePayload : ShortEquityAndIndexQuoteMessagePayload
  deriving DecidableEq, Repr

namespace ShortEquityAndIndexQuoteCategory

def encode (message : ShortEquityAndIndexQuoteCategory) : List UInt8 :=
  encodeUInt 1 (ShortEquityAndIndexQuoteMessagePayload.tag message.shortEquityAndIndexQuoteMessagePayload)
    ++ (ShortEquityAndIndexQuoteMessagePayload.encode message.shortEquityAndIndexQuoteMessagePayload)

def decode (bytes : List UInt8) : Option (ShortEquityAndIndexQuoteCategory × List UInt8) := do
  let (shortEquityAndIndexQuoteMessageType, bytes) ← decodeUInt 1 bytes
  let (shortEquityAndIndexQuoteMessagePayload, bytes) ← ShortEquityAndIndexQuoteMessagePayload.decode shortEquityAndIndexQuoteMessageType bytes
  pure ({ shortEquityAndIndexQuoteMessagePayload }, bytes)

theorem encode_length_pos (message : ShortEquityAndIndexQuoteCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ShortEquityAndIndexQuoteCategory) : (encode message).length ≤ 23 := by
  unfold encode
  cases message.shortEquityAndIndexQuoteMessagePayload with
  | shortEquityAndIndexQuoteMessage inner =>
    simp only [ShortEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage70 inner =>
    simp only [ShortEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage73 inner =>
    simp only [ShortEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage82 inner =>
    simp only [ShortEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage84 inner =>
    simp only [ShortEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage65 inner =>
    simp only [ShortEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage66 inner =>
    simp only [ShortEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage79 inner =>
    simp only [ShortEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage67 inner =>
    simp only [ShortEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage88 inner =>
    simp only [ShortEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, ShortEquityAndIndexQuoteMessage.encode_length]
    omega
  | shortEquityAndIndexQuoteMessage89 inner =>
    simp only [ShortEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length, ShortEquityAndIndexQuoteMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ShortEquityAndIndexQuoteCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ShortEquityAndIndexQuoteMessagePayload.decode_encode, some_bind]
  rfl

end ShortEquityAndIndexQuoteCategory

/-- Administrative Message -/
structure AdministrativeMessage where
  sessionIndicator : BitVec 8
  participantReferenceNumber : BitVec 32
  messageData : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace AdministrativeMessage

def encode (message : AdministrativeMessage) : List UInt8 :=
  encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.messageData.val.length)
    ++ (encodeMany Byte.encode message.messageData.val)))

def decode (bytes : List UInt8) : Option (AdministrativeMessage × List UInt8) := do
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (messageDataLength, bytes) ← decodeUInt 2 bytes
  let (messageData_, bytes) ← decodeMany Byte.decode messageDataLength.toNat bytes
  if fits_messageData : messageData_.length < 256 ^ 2 then
    pure ({ sessionIndicator, participantReferenceNumber, messageData := ⟨messageData_, fits_messageData⟩ }, bytes)
  else none

theorem encode_length_pos (message : AdministrativeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AdministrativeMessage) : (encode message).length ≤ 65542 := by
  have bound_messageData := message.messageData.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : AdministrativeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

/-- Any Administrative Message Payload, selected by Administrative Message Type -/
inductive AdministrativeMessagePayload where
  | administrativeMessage (message : AdministrativeMessage) -- " " 0x20
  deriving DecidableEq, Repr

namespace AdministrativeMessagePayload

/-- The Administrative Message Type each message is sent under -/
def tag : AdministrativeMessagePayload → BitVec 8
  | .administrativeMessage _ => 32

def encode : AdministrativeMessagePayload → List UInt8
  | .administrativeMessage message => AdministrativeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AdministrativeMessagePayload) : (encode message).length ≤ 65542 := by
  cases message with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AdministrativeMessagePayload × List UInt8) :=
  if tag = 32 then (AdministrativeMessage.decode bytes).map fun (message, rest) => (.administrativeMessage message, rest)
  else none

@[simp] theorem decode_encode (message : AdministrativeMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end AdministrativeMessagePayload

/-- Administrative Category -/
structure AdministrativeCategory where
  administrativeMessagePayload : AdministrativeMessagePayload
  deriving DecidableEq, Repr

namespace AdministrativeCategory

def encode (message : AdministrativeCategory) : List UInt8 :=
  encodeUInt 1 (AdministrativeMessagePayload.tag message.administrativeMessagePayload)
    ++ (AdministrativeMessagePayload.encode message.administrativeMessagePayload)

def decode (bytes : List UInt8) : Option (AdministrativeCategory × List UInt8) := do
  let (administrativeMessageType, bytes) ← decodeUInt 1 bytes
  let (administrativeMessagePayload, bytes) ← AdministrativeMessagePayload.decode administrativeMessageType bytes
  pure ({ administrativeMessagePayload }, bytes)

theorem encode_length_pos (message : AdministrativeCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AdministrativeCategory) : (encode message).length ≤ 65543 := by
  unfold encode
  cases message.administrativeMessagePayload with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : AdministrativeCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [AdministrativeMessagePayload.decode_encode, some_bind]
  rfl

end AdministrativeCategory

/-- Control Message: 5 bytes -/
structure ControlMessage where
  sessionIndicator : BitVec 8
  participantReferenceNumber : BitVec 32
  deriving DecidableEq, Repr

namespace ControlMessage

def encode (message : ControlMessage) : List UInt8 :=
  encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.participantReferenceNumber)

def decode (bytes : List UInt8) : Option (ControlMessage × List UInt8) := do
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  pure ({ sessionIndicator, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : ControlMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ControlMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ControlMessage

/-- Any Control Message Payload, selected by Control Message Type -/
inductive ControlMessagePayload where
  | controlMessage (message : ControlMessage) -- "C" 0x43
  | controlMessage69 (message : ControlMessage) -- "E" 0x45
  | controlMessage70 (message : ControlMessage) -- "F" 0x46
  | controlMessage74 (message : ControlMessage) -- "J" 0x4A
  | controlMessage79 (message : ControlMessage) -- "O" 0x4F
  deriving DecidableEq, Repr

namespace ControlMessagePayload

/-- The Control Message Type each message is sent under -/
def tag : ControlMessagePayload → BitVec 8
  | .controlMessage _ => 67
  | .controlMessage69 _ => 69
  | .controlMessage70 _ => 70
  | .controlMessage74 _ => 74
  | .controlMessage79 _ => 79

def encode : ControlMessagePayload → List UInt8
  | .controlMessage message => ControlMessage.encode message
  | .controlMessage69 message => ControlMessage.encode message
  | .controlMessage70 message => ControlMessage.encode message
  | .controlMessage74 message => ControlMessage.encode message
  | .controlMessage79 message => ControlMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ControlMessagePayload) : (encode message).length ≤ 5 := by
  cases message with
  | controlMessage inner =>
    simp only [encode, ControlMessage.encode_length]
    omega
  | controlMessage69 inner =>
    simp only [encode, ControlMessage.encode_length]
    omega
  | controlMessage70 inner =>
    simp only [encode, ControlMessage.encode_length]
    omega
  | controlMessage74 inner =>
    simp only [encode, ControlMessage.encode_length]
    omega
  | controlMessage79 inner =>
    simp only [encode, ControlMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ControlMessagePayload × List UInt8) :=
  if tag = 67 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage message, rest)
  else if tag = 69 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage69 message, rest)
  else if tag = 70 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage70 message, rest)
  else if tag = 74 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage74 message, rest)
  else if tag = 79 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage79 message, rest)
  else none

@[simp] theorem decode_encode (message : ControlMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ControlMessagePayload

/-- Control Category -/
structure ControlCategory where
  controlMessagePayload : ControlMessagePayload
  deriving DecidableEq, Repr

namespace ControlCategory

def encode (message : ControlCategory) : List UInt8 :=
  encodeUInt 1 (ControlMessagePayload.tag message.controlMessagePayload)
    ++ (ControlMessagePayload.encode message.controlMessagePayload)

def decode (bytes : List UInt8) : Option (ControlCategory × List UInt8) := do
  let (controlMessageType, bytes) ← decodeUInt 1 bytes
  let (controlMessagePayload, bytes) ← ControlMessagePayload.decode controlMessageType bytes
  pure ({ controlMessagePayload }, bytes)

theorem encode_length_pos (message : ControlCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ControlCategory) : (encode message).length ≤ 6 := by
  unfold encode
  cases message.controlMessagePayload with
  | controlMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, ControlMessage.encode_length]
    omega
  | controlMessage69 inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, ControlMessage.encode_length]
    omega
  | controlMessage70 inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, ControlMessage.encode_length]
    omega
  | controlMessage74 inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, ControlMessage.encode_length]
    omega
  | controlMessage79 inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, ControlMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ControlCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ControlMessagePayload.decode_encode, some_bind]
  rfl

end ControlCategory

/-- Block Sequence Number Status Inquiry Request Message: 13 bytes -/
structure BlockSequenceNumberStatusInquiryRequestMessage where
  sessionIndicator : BitVec 8
  participantReferenceNumber : BitVec 32
  reserved4 : Alpha 4
  secondReserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace BlockSequenceNumberStatusInquiryRequestMessage

def encode (message : BlockSequenceNumberStatusInquiryRequestMessage) : List UInt8 :=
  encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.secondReserved4)))

def decode (bytes : List UInt8) : Option (BlockSequenceNumberStatusInquiryRequestMessage × List UInt8) := do
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (secondReserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ sessionIndicator, participantReferenceNumber, reserved4, secondReserved4 }, bytes)

@[simp] theorem encode_length (message : BlockSequenceNumberStatusInquiryRequestMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BlockSequenceNumberStatusInquiryRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BlockSequenceNumberStatusInquiryRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BlockSequenceNumberStatusInquiryRequestMessage

/-- Block Sequence Number Status Response Message: 13 bytes -/
structure BlockSequenceNumberStatusResponseMessage where
  sessionIndicator : BitVec 8
  participantReferenceNumber : BitVec 32
  blockSequenceNumber : BitVec 32
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace BlockSequenceNumberStatusResponseMessage

def encode (message : BlockSequenceNumberStatusResponseMessage) : List UInt8 :=
  encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (encodeUInt 4 message.blockSequenceNumber
    ++ (Alpha.encode message.reserved4)))

def decode (bytes : List UInt8) : Option (BlockSequenceNumberStatusResponseMessage × List UInt8) := do
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ sessionIndicator, participantReferenceNumber, blockSequenceNumber, reserved4 }, bytes)

@[simp] theorem encode_length (message : BlockSequenceNumberStatusResponseMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BlockSequenceNumberStatusResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BlockSequenceNumberStatusResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BlockSequenceNumberStatusResponseMessage

/-- Message Count Status Inquiry Request Message: 13 bytes -/
structure MessageCountStatusInquiryRequestMessage where
  sessionIndicator : BitVec 8
  participantReferenceNumber : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace MessageCountStatusInquiryRequestMessage

def encode (message : MessageCountStatusInquiryRequestMessage) : List UInt8 :=
  encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.reserved8))

def decode (bytes : List UInt8) : Option (MessageCountStatusInquiryRequestMessage × List UInt8) := do
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ sessionIndicator, participantReferenceNumber, reserved8 }, bytes)

@[simp] theorem encode_length (message : MessageCountStatusInquiryRequestMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MessageCountStatusInquiryRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageCountStatusInquiryRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MessageCountStatusInquiryRequestMessage

/-- Message Count Status Response Message: 13 bytes -/
structure MessageCountStatusResponseMessage where
  sessionIndicator : BitVec 8
  participantReferenceNumber : BitVec 32
  messageCount : BitVec 64
  deriving DecidableEq, Repr

namespace MessageCountStatusResponseMessage

def encode (message : MessageCountStatusResponseMessage) : List UInt8 :=
  encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (encodeUInt 8 message.messageCount))

def decode (bytes : List UInt8) : Option (MessageCountStatusResponseMessage × List UInt8) := do
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (messageCount, bytes) ← decodeUInt 8 bytes
  pure ({ sessionIndicator, participantReferenceNumber, messageCount }, bytes)

@[simp] theorem encode_length (message : MessageCountStatusResponseMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : MessageCountStatusResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageCountStatusResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MessageCountStatusResponseMessage

/-- Any Sequence Number Status Message Payload, selected by Sequence Number Status Message Type -/
inductive SequenceNumberStatusMessagePayload where
  | blockSequenceNumberStatusInquiryRequestMessage (message : BlockSequenceNumberStatusInquiryRequestMessage) -- "L" 0x4C
  | blockSequenceNumberStatusResponseMessage (message : BlockSequenceNumberStatusResponseMessage) -- "M" 0x4D
  | messageCountStatusInquiryRequestMessage (message : MessageCountStatusInquiryRequestMessage) -- "R" 0x52
  | messageCountStatusResponseMessage (message : MessageCountStatusResponseMessage) -- "S" 0x53
  deriving DecidableEq, Repr

namespace SequenceNumberStatusMessagePayload

/-- The Sequence Number Status Message Type each message is sent under -/
def tag : SequenceNumberStatusMessagePayload → BitVec 8
  | .blockSequenceNumberStatusInquiryRequestMessage _ => 76
  | .blockSequenceNumberStatusResponseMessage _ => 77
  | .messageCountStatusInquiryRequestMessage _ => 82
  | .messageCountStatusResponseMessage _ => 83

def encode : SequenceNumberStatusMessagePayload → List UInt8
  | .blockSequenceNumberStatusInquiryRequestMessage message => BlockSequenceNumberStatusInquiryRequestMessage.encode message
  | .blockSequenceNumberStatusResponseMessage message => BlockSequenceNumberStatusResponseMessage.encode message
  | .messageCountStatusInquiryRequestMessage message => MessageCountStatusInquiryRequestMessage.encode message
  | .messageCountStatusResponseMessage message => MessageCountStatusResponseMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequenceNumberStatusMessagePayload) : (encode message).length ≤ 13 := by
  cases message with
  | blockSequenceNumberStatusInquiryRequestMessage inner =>
    simp only [encode, BlockSequenceNumberStatusInquiryRequestMessage.encode_length]
    omega
  | blockSequenceNumberStatusResponseMessage inner =>
    simp only [encode, BlockSequenceNumberStatusResponseMessage.encode_length]
    omega
  | messageCountStatusInquiryRequestMessage inner =>
    simp only [encode, MessageCountStatusInquiryRequestMessage.encode_length]
    omega
  | messageCountStatusResponseMessage inner =>
    simp only [encode, MessageCountStatusResponseMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequenceNumberStatusMessagePayload × List UInt8) :=
  if tag = 76 then (BlockSequenceNumberStatusInquiryRequestMessage.decode bytes).map fun (message, rest) => (.blockSequenceNumberStatusInquiryRequestMessage message, rest)
  else if tag = 77 then (BlockSequenceNumberStatusResponseMessage.decode bytes).map fun (message, rest) => (.blockSequenceNumberStatusResponseMessage message, rest)
  else if tag = 82 then (MessageCountStatusInquiryRequestMessage.decode bytes).map fun (message, rest) => (.messageCountStatusInquiryRequestMessage message, rest)
  else if tag = 83 then (MessageCountStatusResponseMessage.decode bytes).map fun (message, rest) => (.messageCountStatusResponseMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequenceNumberStatusMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequenceNumberStatusMessagePayload

/-- Sequence Number Status Category -/
structure SequenceNumberStatusCategory where
  sequenceNumberStatusMessagePayload : SequenceNumberStatusMessagePayload
  deriving DecidableEq, Repr

namespace SequenceNumberStatusCategory

def encode (message : SequenceNumberStatusCategory) : List UInt8 :=
  encodeUInt 1 (SequenceNumberStatusMessagePayload.tag message.sequenceNumberStatusMessagePayload)
    ++ (SequenceNumberStatusMessagePayload.encode message.sequenceNumberStatusMessagePayload)

def decode (bytes : List UInt8) : Option (SequenceNumberStatusCategory × List UInt8) := do
  let (sequenceNumberStatusMessageType, bytes) ← decodeUInt 1 bytes
  let (sequenceNumberStatusMessagePayload, bytes) ← SequenceNumberStatusMessagePayload.decode sequenceNumberStatusMessageType bytes
  pure ({ sequenceNumberStatusMessagePayload }, bytes)

theorem encode_length_pos (message : SequenceNumberStatusCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequenceNumberStatusCategory) : (encode message).length ≤ 14 := by
  unfold encode
  cases message.sequenceNumberStatusMessagePayload with
  | blockSequenceNumberStatusInquiryRequestMessage inner =>
    simp only [SequenceNumberStatusMessagePayload.encode, List.length_append, encodeUInt_length, BlockSequenceNumberStatusInquiryRequestMessage.encode_length]
    omega
  | blockSequenceNumberStatusResponseMessage inner =>
    simp only [SequenceNumberStatusMessagePayload.encode, List.length_append, encodeUInt_length, BlockSequenceNumberStatusResponseMessage.encode_length]
    omega
  | messageCountStatusInquiryRequestMessage inner =>
    simp only [SequenceNumberStatusMessagePayload.encode, List.length_append, encodeUInt_length, MessageCountStatusInquiryRequestMessage.encode_length]
    omega
  | messageCountStatusResponseMessage inner =>
    simp only [SequenceNumberStatusMessagePayload.encode, List.length_append, encodeUInt_length, MessageCountStatusResponseMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequenceNumberStatusCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequenceNumberStatusMessagePayload.decode_encode, some_bind]
  rfl

end SequenceNumberStatusCategory

/-- Underlying Value Last Sale Message: 20 bytes -/
structure UnderlyingValueLastSaleMessage where
  sessionIndicator : BitVec 8
  participantReferenceNumber : BitVec 32
  securitySymbol : Alpha 5
  reserved1 : Alpha 1
  indexValueDenominatorCode : IndexValueDenominatorCode
  indexValue : BitVec 32
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace UnderlyingValueLastSaleMessage

def encode (message : UnderlyingValueLastSaleMessage) : List UInt8 :=
  encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.reserved1
    ++ (IndexValueDenominatorCode.encode message.indexValueDenominatorCode
    ++ (encodeUInt 4 message.indexValue
    ++ (Alpha.encode message.reserved4))))))

def decode (bytes : List UInt8) : Option (UnderlyingValueLastSaleMessage × List UInt8) := do
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (indexValueDenominatorCode, bytes) ← IndexValueDenominatorCode.decode bytes
  let (indexValue, bytes) ← decodeUInt 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ sessionIndicator, participantReferenceNumber, securitySymbol, reserved1, indexValueDenominatorCode, indexValue, reserved4 }, bytes)

@[simp] theorem encode_length (message : UnderlyingValueLastSaleMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, IndexValueDenominatorCode.encode_length]

theorem encode_length_pos (message : UnderlyingValueLastSaleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingValueLastSaleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IndexValueDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingValueLastSaleMessage

/-- Underlying Value Bid And Offer Message: 20 bytes -/
structure UnderlyingValueBidAndOfferMessage where
  sessionIndicator : BitVec 8
  participantReferenceNumber : BitVec 32
  securitySymbol : Alpha 5
  reserved1 : Alpha 1
  indexValueDenominatorCode : IndexValueDenominatorCode
  bidIndexValue : BitVec 32
  offerIndexValue : BitVec 32
  deriving DecidableEq, Repr

namespace UnderlyingValueBidAndOfferMessage

def encode (message : UnderlyingValueBidAndOfferMessage) : List UInt8 :=
  encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.reserved1
    ++ (IndexValueDenominatorCode.encode message.indexValueDenominatorCode
    ++ (encodeUInt 4 message.bidIndexValue
    ++ (encodeUInt 4 message.offerIndexValue))))))

def decode (bytes : List UInt8) : Option (UnderlyingValueBidAndOfferMessage × List UInt8) := do
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (indexValueDenominatorCode, bytes) ← IndexValueDenominatorCode.decode bytes
  let (bidIndexValue, bytes) ← decodeUInt 4 bytes
  let (offerIndexValue, bytes) ← decodeUInt 4 bytes
  pure ({ sessionIndicator, participantReferenceNumber, securitySymbol, reserved1, indexValueDenominatorCode, bidIndexValue, offerIndexValue }, bytes)

@[simp] theorem encode_length (message : UnderlyingValueBidAndOfferMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, IndexValueDenominatorCode.encode_length]

theorem encode_length_pos (message : UnderlyingValueBidAndOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingValueBidAndOfferMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IndexValueDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end UnderlyingValueBidAndOfferMessage

/-- Any Underlying Value Message Message Payload, selected by Underlying Value Message Message Type -/
inductive UnderlyingValueMessageMessagePayload where
  | underlyingValueLastSaleMessage (message : UnderlyingValueLastSaleMessage) -- " " 0x20
  | underlyingValueBidAndOfferMessage (message : UnderlyingValueBidAndOfferMessage) -- "I" 0x49
  deriving DecidableEq, Repr

namespace UnderlyingValueMessageMessagePayload

/-- The Underlying Value Message Message Type each message is sent under -/
def tag : UnderlyingValueMessageMessagePayload → BitVec 8
  | .underlyingValueLastSaleMessage _ => 32
  | .underlyingValueBidAndOfferMessage _ => 73

def encode : UnderlyingValueMessageMessagePayload → List UInt8
  | .underlyingValueLastSaleMessage message => UnderlyingValueLastSaleMessage.encode message
  | .underlyingValueBidAndOfferMessage message => UnderlyingValueBidAndOfferMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnderlyingValueMessageMessagePayload) : (encode message).length ≤ 20 := by
  cases message with
  | underlyingValueLastSaleMessage inner =>
    simp only [encode, UnderlyingValueLastSaleMessage.encode_length]
    omega
  | underlyingValueBidAndOfferMessage inner =>
    simp only [encode, UnderlyingValueBidAndOfferMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnderlyingValueMessageMessagePayload × List UInt8) :=
  if tag = 32 then (UnderlyingValueLastSaleMessage.decode bytes).map fun (message, rest) => (.underlyingValueLastSaleMessage message, rest)
  else if tag = 73 then (UnderlyingValueBidAndOfferMessage.decode bytes).map fun (message, rest) => (.underlyingValueBidAndOfferMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UnderlyingValueMessageMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnderlyingValueMessageMessagePayload

/-- Underlying Value Message Category -/
structure UnderlyingValueMessageCategory where
  underlyingValueMessageMessagePayload : UnderlyingValueMessageMessagePayload
  deriving DecidableEq, Repr

namespace UnderlyingValueMessageCategory

def encode (message : UnderlyingValueMessageCategory) : List UInt8 :=
  encodeUInt 1 (UnderlyingValueMessageMessagePayload.tag message.underlyingValueMessageMessagePayload)
    ++ (UnderlyingValueMessageMessagePayload.encode message.underlyingValueMessageMessagePayload)

def decode (bytes : List UInt8) : Option (UnderlyingValueMessageCategory × List UInt8) := do
  let (underlyingValueMessageMessageType, bytes) ← decodeUInt 1 bytes
  let (underlyingValueMessageMessagePayload, bytes) ← UnderlyingValueMessageMessagePayload.decode underlyingValueMessageMessageType bytes
  pure ({ underlyingValueMessageMessagePayload }, bytes)

theorem encode_length_pos (message : UnderlyingValueMessageCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnderlyingValueMessageCategory) : (encode message).length ≤ 21 := by
  unfold encode
  cases message.underlyingValueMessageMessagePayload with
  | underlyingValueLastSaleMessage inner =>
    simp only [UnderlyingValueMessageMessagePayload.encode, List.length_append, encodeUInt_length, UnderlyingValueLastSaleMessage.encode_length]
    omega
  | underlyingValueBidAndOfferMessage inner =>
    simp only [UnderlyingValueMessageMessagePayload.encode, List.length_append, encodeUInt_length, UnderlyingValueBidAndOfferMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : UnderlyingValueMessageCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnderlyingValueMessageMessagePayload.decode_encode, some_bind]
  rfl

end UnderlyingValueMessageCategory

/-- Any Payload, selected by Message Category -/
inductive Payload where
  | equityAndIndexLastSaleCategory (message : EquityAndIndexLastSaleCategory) -- "a" 0x61
  | equityAndIndexEndOfDaySummaryCategory (message : EquityAndIndexEndOfDaySummaryCategory) -- "f" 0x66
  | longEquityAndIndexQuoteCategory (message : LongEquityAndIndexQuoteCategory) -- "k" 0x6B
  | shortEquityAndIndexQuoteCategory (message : ShortEquityAndIndexQuoteCategory) -- "q" 0x71
  | administrativeCategory (message : AdministrativeCategory) -- "C" 0x43
  | controlCategory (message : ControlCategory) -- "H" 0x48
  | sequenceNumberStatusCategory (message : SequenceNumberStatusCategory) -- "N" 0x4E
  | underlyingValueMessageCategory (message : UnderlyingValueMessageCategory) -- "Y" 0x59
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Category each message is sent under -/
def tag : Payload → BitVec 8
  | .equityAndIndexLastSaleCategory _ => 97
  | .equityAndIndexEndOfDaySummaryCategory _ => 102
  | .longEquityAndIndexQuoteCategory _ => 107
  | .shortEquityAndIndexQuoteCategory _ => 113
  | .administrativeCategory _ => 67
  | .controlCategory _ => 72
  | .sequenceNumberStatusCategory _ => 78
  | .underlyingValueMessageCategory _ => 89

def encode : Payload → List UInt8
  | .equityAndIndexLastSaleCategory message => EquityAndIndexLastSaleCategory.encode message
  | .equityAndIndexEndOfDaySummaryCategory message => EquityAndIndexEndOfDaySummaryCategory.encode message
  | .longEquityAndIndexQuoteCategory message => LongEquityAndIndexQuoteCategory.encode message
  | .shortEquityAndIndexQuoteCategory message => ShortEquityAndIndexQuoteCategory.encode message
  | .administrativeCategory message => AdministrativeCategory.encode message
  | .controlCategory message => ControlCategory.encode message
  | .sequenceNumberStatusCategory message => SequenceNumberStatusCategory.encode message
  | .underlyingValueMessageCategory message => UnderlyingValueMessageCategory.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 65543 := by
  cases message with
  | equityAndIndexLastSaleCategory inner =>
    have bound_inner := EquityAndIndexLastSaleCategory.encode_length_le inner
    simp only [encode]
    omega
  | equityAndIndexEndOfDaySummaryCategory inner =>
    have bound_inner := EquityAndIndexEndOfDaySummaryCategory.encode_length_le inner
    simp only [encode]
    omega
  | longEquityAndIndexQuoteCategory inner =>
    have bound_inner := LongEquityAndIndexQuoteCategory.encode_length_le inner
    simp only [encode]
    omega
  | shortEquityAndIndexQuoteCategory inner =>
    have bound_inner := ShortEquityAndIndexQuoteCategory.encode_length_le inner
    simp only [encode]
    omega
  | administrativeCategory inner =>
    have bound_inner := AdministrativeCategory.encode_length_le inner
    simp only [encode]
    omega
  | controlCategory inner =>
    have bound_inner := ControlCategory.encode_length_le inner
    simp only [encode]
    omega
  | sequenceNumberStatusCategory inner =>
    have bound_inner := SequenceNumberStatusCategory.encode_length_le inner
    simp only [encode]
    omega
  | underlyingValueMessageCategory inner =>
    have bound_inner := UnderlyingValueMessageCategory.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 97 then (EquityAndIndexLastSaleCategory.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleCategory message, rest)
  else if tag = 102 then (EquityAndIndexEndOfDaySummaryCategory.decode bytes).map fun (message, rest) => (.equityAndIndexEndOfDaySummaryCategory message, rest)
  else if tag = 107 then (LongEquityAndIndexQuoteCategory.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteCategory message, rest)
  else if tag = 113 then (ShortEquityAndIndexQuoteCategory.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteCategory message, rest)
  else if tag = 67 then (AdministrativeCategory.decode bytes).map fun (message, rest) => (.administrativeCategory message, rest)
  else if tag = 72 then (ControlCategory.decode bytes).map fun (message, rest) => (.controlCategory message, rest)
  else if tag = 78 then (SequenceNumberStatusCategory.decode bytes).map fun (message, rest) => (.sequenceNumberStatusCategory message, rest)
  else if tag = 89 then (UnderlyingValueMessageCategory.decode bytes).map fun (message, rest) => (.underlyingValueMessageCategory message, rest)
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
theorem encode_length_le (message : Message) : (encode message).length ≤ 65545 := by
  unfold encode
  cases message.payload with
  | equityAndIndexLastSaleCategory inner =>
    have bound_inner := EquityAndIndexLastSaleCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | equityAndIndexEndOfDaySummaryCategory inner =>
    have bound_inner := EquityAndIndexEndOfDaySummaryCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | longEquityAndIndexQuoteCategory inner =>
    have bound_inner := LongEquityAndIndexQuoteCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | shortEquityAndIndexQuoteCategory inner =>
    have bound_inner := ShortEquityAndIndexQuoteCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | administrativeCategory inner =>
    have bound_inner := AdministrativeCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | controlCategory inner =>
    have bound_inner := ControlCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | sequenceNumberStatusCategory inner =>
    have bound_inner := SequenceNumberStatusCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | underlyingValueMessageCategory inner =>
    have bound_inner := UnderlyingValueMessageCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
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
  blockSeparator : BitVec 16
  version : BitVec 8
  blockSize : BitVec 16
  reserved : BitVec 8
  secondReserved : BitVec 8
  thirdReserved : BitVec 8
  blockSequenceNumber : BitVec 32
  blockTimestamp : BlockTimestamp
  blockChecksum : BitVec 16
  message : Bounded 1 Message
  blockPadByte : Capped 1
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 message.blockSeparator
    ++ (encodeUInt 1 message.version
    ++ (encodeUInt 2 message.blockSize
    ++ (encodeUInt 1 message.reserved
    ++ (encodeUInt 1 message.secondReserved
    ++ (encodeUInt 1 message.thirdReserved
    ++ (encodeUInt 4 message.blockSequenceNumber
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (BlockTimestamp.encode message.blockTimestamp
    ++ (encodeUInt 2 message.blockChecksum
    ++ (encodeMany Message.encode message.message.val
    ++ (message.blockPadByte.val)))))))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (blockSeparator, bytes) ← decodeUInt 2 bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (blockSize, bytes) ← decodeUInt 2 bytes
  let (reserved, bytes) ← decodeUInt 1 bytes
  let (secondReserved, bytes) ← decodeUInt 1 bytes
  let (thirdReserved, bytes) ← decodeUInt 1 bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (messagesInBlock, bytes) ← decodeUInt 1 bytes
  let (blockTimestamp, bytes) ← BlockTimestamp.decode bytes
  let (blockChecksum, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messagesInBlock.toNat bytes
  let blockPadByte_ := bytes
  if fits_message : message_.length < 256 ^ 1 then
    if fits_blockPadByte : blockPadByte_.length ≤ 1 then
      pure { blockSeparator, version, blockSize, reserved, secondReserved, thirdReserved, blockSequenceNumber, blockTimestamp, blockChecksum, message := ⟨message_, fits_message⟩, blockPadByte := ⟨blockPadByte_, fits_blockPadByte⟩ }
    else none
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 16713999 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 65545 Message.encode_length_le message.message.val
  have bound_blockPadByte := message.blockPadByte.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, BlockTimestamp.encode_length]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
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

end Omi.SiacOpraInputObiV50I
