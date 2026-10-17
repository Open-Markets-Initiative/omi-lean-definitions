import Wire

/-!
# Bolsas y Mercados Españoles MEFF Order Entry v1.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BmeMeffOrderentryBmegateV16

/-- Settl Method: one byte code -/
def SettlMethod.codes : List UInt8 :=
  [0x43, 0x50]

inductive SettlMethod where
  | cash -- Cash
  | physical -- Physical
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlMethod.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlMethod

def toByte : SettlMethod → UInt8
  | .cash => 0x43
  | .physical => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlMethod :=
  if byte = 0x43 then .cash
  else .physical

def ofByte (byte : UInt8) : SettlMethod :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlMethod) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | physical => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlMethod) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlMethod × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlMethod) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlMethod) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlMethod) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlMethod

/-- Exercise Style: one byte code -/
def ExerciseStyle.codes : List UInt8 :=
  [0x41, 0x45, 0x56]

inductive ExerciseStyle where
  | american -- American
  | european -- European
  | europeanAutomatic -- European Automatic
  | unlisted (byte : { byte : UInt8 // byte ∉ ExerciseStyle.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExerciseStyle

def toByte : ExerciseStyle → UInt8
  | .american => 0x41
  | .european => 0x45
  | .europeanAutomatic => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExerciseStyle :=
  if byte = 0x41 then .american
  else if byte = 0x45 then .european
  else .europeanAutomatic

def ofByte (byte : UInt8) : ExerciseStyle :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExerciseStyle) : ofByte value.toByte = value := by
  cases value with
  | american => decide
  | european => decide
  | europeanAutomatic => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExerciseStyle) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExerciseStyle × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExerciseStyle) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExerciseStyle) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExerciseStyle) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExerciseStyle

/-- Put Or Call: one byte code -/
def PutOrCall.codes : List UInt8 :=
  [0x43, 0x50, 0x4F]

inductive PutOrCall where
  | call -- Call
  | put -- Put
  | other -- Other
  | unlisted (byte : { byte : UInt8 // byte ∉ PutOrCall.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PutOrCall

def toByte : PutOrCall → UInt8
  | .call => 0x43
  | .put => 0x50
  | .other => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PutOrCall :=
  if byte = 0x43 then .call
  else if byte = 0x50 then .put
  else .other

def ofByte (byte : UInt8) : PutOrCall :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PutOrCall) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | other => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PutOrCall) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PutOrCall × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PutOrCall) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PutOrCall) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PutOrCall) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PutOrCall

/-- Flexible Indicator: one byte code -/
def FlexibleIndicator.codes : List UInt8 :=
  [0x59, 0x4E]

inductive FlexibleIndicator where
  | flexible -- Flexible
  | standard -- Standard
  | unlisted (byte : { byte : UInt8 // byte ∉ FlexibleIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FlexibleIndicator

def toByte : FlexibleIndicator → UInt8
  | .flexible => 0x59
  | .standard => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FlexibleIndicator :=
  if byte = 0x59 then .flexible
  else .standard

def ofByte (byte : UInt8) : FlexibleIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FlexibleIndicator) : ofByte value.toByte = value := by
  cases value with
  | flexible => decide
  | standard => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FlexibleIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FlexibleIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FlexibleIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : FlexibleIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : FlexibleIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FlexibleIndicator

/-- Adjustments Rule: one byte code -/
def AdjustmentsRule.codes : List UInt8 :=
  [0x45, 0x54]

inductive AdjustmentsRule where
  | extraordinaryDividendAdjustmentsOnly -- Extraordinary Dividend Adjustments Only
  | total -- Total
  | unlisted (byte : { byte : UInt8 // byte ∉ AdjustmentsRule.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AdjustmentsRule

def toByte : AdjustmentsRule → UInt8
  | .extraordinaryDividendAdjustmentsOnly => 0x45
  | .total => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AdjustmentsRule :=
  if byte = 0x45 then .extraordinaryDividendAdjustmentsOnly
  else .total

def ofByte (byte : UInt8) : AdjustmentsRule :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AdjustmentsRule) : ofByte value.toByte = value := by
  cases value with
  | extraordinaryDividendAdjustmentsOnly => decide
  | total => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AdjustmentsRule) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AdjustmentsRule × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AdjustmentsRule) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AdjustmentsRule) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AdjustmentsRule) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AdjustmentsRule

/-- Commodity Derivative Indicator: one byte code -/
def CommodityDerivativeIndicator.codes : List UInt8 :=
  [0x53, 0x4E, 0x44]

inductive CommodityDerivativeIndicator where
  | commodityDerivative -- Commodity Derivative
  | nonDerivative -- Non Derivative
  | derivative -- Derivative
  | unlisted (byte : { byte : UInt8 // byte ∉ CommodityDerivativeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CommodityDerivativeIndicator

def toByte : CommodityDerivativeIndicator → UInt8
  | .commodityDerivative => 0x53
  | .nonDerivative => 0x4E
  | .derivative => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CommodityDerivativeIndicator :=
  if byte = 0x53 then .commodityDerivative
  else if byte = 0x4E then .nonDerivative
  else .derivative

def ofByte (byte : UInt8) : CommodityDerivativeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CommodityDerivativeIndicator) : ofByte value.toByte = value := by
  cases value with
  | commodityDerivative => decide
  | nonDerivative => decide
  | derivative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CommodityDerivativeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CommodityDerivativeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CommodityDerivativeIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CommodityDerivativeIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CommodityDerivativeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CommodityDerivativeIndicator

/-- Maturity Month Year Increment Units: one byte code -/
def MaturityMonthYearIncrementUnits.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33]

inductive MaturityMonthYearIncrementUnits where
  | months -- Months
  | days -- Days
  | weeks -- Weeks
  | years -- Years
  | unlisted (byte : { byte : UInt8 // byte ∉ MaturityMonthYearIncrementUnits.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MaturityMonthYearIncrementUnits

def toByte : MaturityMonthYearIncrementUnits → UInt8
  | .months => 0x30
  | .days => 0x31
  | .weeks => 0x32
  | .years => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MaturityMonthYearIncrementUnits :=
  if byte = 0x30 then .months
  else if byte = 0x31 then .days
  else if byte = 0x32 then .weeks
  else .years

def ofByte (byte : UInt8) : MaturityMonthYearIncrementUnits :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MaturityMonthYearIncrementUnits) : ofByte value.toByte = value := by
  cases value with
  | months => decide
  | days => decide
  | weeks => decide
  | years => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MaturityMonthYearIncrementUnits) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MaturityMonthYearIncrementUnits × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MaturityMonthYearIncrementUnits) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MaturityMonthYearIncrementUnits) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MaturityMonthYearIncrementUnits) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MaturityMonthYearIncrementUnits

/-- X Rolling Closing Type: one byte code -/
def XRollingClosingType.codes : List UInt8 :=
  [0x4D, 0x31, 0x32]

inductive XRollingClosingType where
  | marketDefaultValueValueToBeUsedInFlexXRollingWithAClosedExpiryDateAndNoPossibilityToModifyIt -- Market Default Value Value To Be Used In Flex X Rolling With A Closed Expiry Date And No Possibility To Modify It
  | byBuyer -- By Buyer
  | bySeller -- By Seller
  | unlisted (byte : { byte : UInt8 // byte ∉ XRollingClosingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace XRollingClosingType

def toByte : XRollingClosingType → UInt8
  | .marketDefaultValueValueToBeUsedInFlexXRollingWithAClosedExpiryDateAndNoPossibilityToModifyIt => 0x4D
  | .byBuyer => 0x31
  | .bySeller => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : XRollingClosingType :=
  if byte = 0x4D then .marketDefaultValueValueToBeUsedInFlexXRollingWithAClosedExpiryDateAndNoPossibilityToModifyIt
  else if byte = 0x31 then .byBuyer
  else .bySeller

def ofByte (byte : UInt8) : XRollingClosingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : XRollingClosingType) : ofByte value.toByte = value := by
  cases value with
  | marketDefaultValueValueToBeUsedInFlexXRollingWithAClosedExpiryDateAndNoPossibilityToModifyIt => decide
  | byBuyer => decide
  | bySeller => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : XRollingClosingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (XRollingClosingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : XRollingClosingType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : XRollingClosingType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : XRollingClosingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end XRollingClosingType

/-- X Rolling Reference Buyer Rate: one byte code -/
def XRollingReferenceBuyerRate.codes : List UInt8 :=
  [0x53, 0x46, 0x4D, 0x30, 0x20]

inductive XRollingReferenceBuyerRate where
  | strDefaultValueForNonFlexXRolling -- € Str Default Value For Non Flex X Rolling
  | fisAnalitics -- Fis Analitics
  | meffRate -- Meff Rate
  | zero -- Zero
  | naUsedInFlexInTheFinancingLeg -- Na Used In Flex In The Financing Leg
  | unlisted (byte : { byte : UInt8 // byte ∉ XRollingReferenceBuyerRate.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace XRollingReferenceBuyerRate

def toByte : XRollingReferenceBuyerRate → UInt8
  | .strDefaultValueForNonFlexXRolling => 0x53
  | .fisAnalitics => 0x46
  | .meffRate => 0x4D
  | .zero => 0x30
  | .naUsedInFlexInTheFinancingLeg => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : XRollingReferenceBuyerRate :=
  if byte = 0x53 then .strDefaultValueForNonFlexXRolling
  else if byte = 0x46 then .fisAnalitics
  else if byte = 0x4D then .meffRate
  else if byte = 0x30 then .zero
  else .naUsedInFlexInTheFinancingLeg

def ofByte (byte : UInt8) : XRollingReferenceBuyerRate :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : XRollingReferenceBuyerRate) : ofByte value.toByte = value := by
  cases value with
  | strDefaultValueForNonFlexXRolling => decide
  | fisAnalitics => decide
  | meffRate => decide
  | zero => decide
  | naUsedInFlexInTheFinancingLeg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : XRollingReferenceBuyerRate) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (XRollingReferenceBuyerRate × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : XRollingReferenceBuyerRate) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : XRollingReferenceBuyerRate) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : XRollingReferenceBuyerRate) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end XRollingReferenceBuyerRate

/-- X Rolling Reference Seller Rate: one byte code -/
def XRollingReferenceSellerRate.codes : List UInt8 :=
  [0x53, 0x46, 0x4D, 0x30, 0x20]

inductive XRollingReferenceSellerRate where
  | str -- € Str
  | fisAnalitics -- Fis Analitics
  | meffRateDefaultValueForNonFlexXRolling -- Meff Rate Default Value For Non Flex X Rolling
  | cero -- Cero
  | naUsedInFlexInTheFinancingLeg -- Na Used In Flex In The Financing Leg
  | unlisted (byte : { byte : UInt8 // byte ∉ XRollingReferenceSellerRate.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace XRollingReferenceSellerRate

def toByte : XRollingReferenceSellerRate → UInt8
  | .str => 0x53
  | .fisAnalitics => 0x46
  | .meffRateDefaultValueForNonFlexXRolling => 0x4D
  | .cero => 0x30
  | .naUsedInFlexInTheFinancingLeg => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : XRollingReferenceSellerRate :=
  if byte = 0x53 then .str
  else if byte = 0x46 then .fisAnalitics
  else if byte = 0x4D then .meffRateDefaultValueForNonFlexXRolling
  else if byte = 0x30 then .cero
  else .naUsedInFlexInTheFinancingLeg

def ofByte (byte : UInt8) : XRollingReferenceSellerRate :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : XRollingReferenceSellerRate) : ofByte value.toByte = value := by
  cases value with
  | str => decide
  | fisAnalitics => decide
  | meffRateDefaultValueForNonFlexXRolling => decide
  | cero => decide
  | naUsedInFlexInTheFinancingLeg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : XRollingReferenceSellerRate) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (XRollingReferenceSellerRate × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : XRollingReferenceSellerRate) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : XRollingReferenceSellerRate) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : XRollingReferenceSellerRate) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end XRollingReferenceSellerRate

/-- Leg Side 1: one byte code -/
def LegSide1.codes : List UInt8 :=
  [0x31, 0x32]

inductive LegSide1 where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide1

def toByte : LegSide1 → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide1 :=
  if byte = 0x31 then .buy
  else .sell

def ofByte (byte : UInt8) : LegSide1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide1) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSide1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSide1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSide1) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LegSide1) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegSide1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSide1

/-- Leg Side 2: one byte code -/
def LegSide2.codes : List UInt8 :=
  [0x31, 0x32]

inductive LegSide2 where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide2

def toByte : LegSide2 → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide2 :=
  if byte = 0x31 then .buy
  else .sell

def ofByte (byte : UInt8) : LegSide2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide2) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSide2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSide2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSide2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LegSide2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegSide2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSide2

/-- Leg Side 3: one byte code -/
def LegSide3.codes : List UInt8 :=
  [0x31, 0x32]

inductive LegSide3 where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide3

def toByte : LegSide3 → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide3 :=
  if byte = 0x31 then .buy
  else .sell

def ofByte (byte : UInt8) : LegSide3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide3) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSide3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSide3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSide3) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LegSide3) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegSide3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSide3

/-- Leg Side 4: one byte code -/
def LegSide4.codes : List UInt8 :=
  [0x31, 0x32]

inductive LegSide4 where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide4

def toByte : LegSide4 → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide4 :=
  if byte = 0x31 then .buy
  else .sell

def ofByte (byte : UInt8) : LegSide4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide4) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSide4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSide4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSide4) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LegSide4) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegSide4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSide4

/-- Leg Side 5: one byte code -/
def LegSide5.codes : List UInt8 :=
  [0x31, 0x32]

inductive LegSide5 where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide5.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide5

def toByte : LegSide5 → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide5 :=
  if byte = 0x31 then .buy
  else .sell

def ofByte (byte : UInt8) : LegSide5 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide5) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSide5) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSide5 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSide5) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LegSide5) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegSide5) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSide5

/-- Ioi Trans Type: one byte code -/
def IoiTransType.codes : List UInt8 :=
  [0x4E, 0x43, 0x52]

inductive IoiTransType where
  | new -- New
  | cancel -- Cancel
  | replace -- Replace
  | unlisted (byte : { byte : UInt8 // byte ∉ IoiTransType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IoiTransType

def toByte : IoiTransType → UInt8
  | .new => 0x4E
  | .cancel => 0x43
  | .replace => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IoiTransType :=
  if byte = 0x4E then .new
  else if byte = 0x43 then .cancel
  else .replace

def ofByte (byte : UInt8) : IoiTransType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IoiTransType) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | cancel => decide
  | replace => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IoiTransType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IoiTransType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IoiTransType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IoiTransType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IoiTransType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IoiTransType

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32, 0x37, 0x3F]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | undisclosed -- Undisclosed
  | notspecified -- Notspecified
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .undisclosed => 0x37
  | .notspecified => 0x3F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
  else if byte = 0x32 then .sell
  else if byte = 0x37 then .undisclosed
  else .notspecified

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | undisclosed => decide
  | notspecified => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Side) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Ioi Qlty Ind: one byte code -/
def IoiQltyInd.codes : List UInt8 :=
  [0x48, 0x4D]

inductive IoiQltyInd where
  | highRfqRequested -- High Rfq Requested
  | mediumOrderRequested -- Medium Order Requested
  | unlisted (byte : { byte : UInt8 // byte ∉ IoiQltyInd.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IoiQltyInd

def toByte : IoiQltyInd → UInt8
  | .highRfqRequested => 0x48
  | .mediumOrderRequested => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IoiQltyInd :=
  if byte = 0x48 then .highRfqRequested
  else .mediumOrderRequested

def ofByte (byte : UInt8) : IoiQltyInd :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IoiQltyInd) : ofByte value.toByte = value := by
  cases value with
  | highRfqRequested => decide
  | mediumOrderRequested => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IoiQltyInd) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IoiQltyInd × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IoiQltyInd) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IoiQltyInd) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IoiQltyInd) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IoiQltyInd

/-- Last Capacity: one byte code -/
def LastCapacity.codes : List UInt8 :=
  [0x44, 0x4D, 0x41]

inductive LastCapacity where
  | dealingOnOwnAccount -- Dealing On Own Account
  | matchedPrincipal -- Matched Principal
  | anyOtherTradingCapacityBlanco -- Any Other Trading Capacity Blanco
  | unlisted (byte : { byte : UInt8 // byte ∉ LastCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LastCapacity

def toByte : LastCapacity → UInt8
  | .dealingOnOwnAccount => 0x44
  | .matchedPrincipal => 0x4D
  | .anyOtherTradingCapacityBlanco => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LastCapacity :=
  if byte = 0x44 then .dealingOnOwnAccount
  else if byte = 0x4D then .matchedPrincipal
  else .anyOtherTradingCapacityBlanco

def ofByte (byte : UInt8) : LastCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LastCapacity) : ofByte value.toByte = value := by
  cases value with
  | dealingOnOwnAccount => decide
  | matchedPrincipal => decide
  | anyOtherTradingCapacityBlanco => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LastCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LastCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LastCapacity) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LastCapacity) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LastCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LastCapacity

/-- Persistence: one byte code -/
def Persistence.codes : List UInt8 :=
  [0x43, 0x50]

inductive Persistence where
  | cancelOnDisconnection -- Cancel On Disconnection
  | persistOnDisconnection -- Persist On Disconnection
  | unlisted (byte : { byte : UInt8 // byte ∉ Persistence.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Persistence

def toByte : Persistence → UInt8
  | .cancelOnDisconnection => 0x43
  | .persistOnDisconnection => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Persistence :=
  if byte = 0x43 then .cancelOnDisconnection
  else .persistOnDisconnection

def ofByte (byte : UInt8) : Persistence :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Persistence) : ofByte value.toByte = value := by
  cases value with
  | cancelOnDisconnection => decide
  | persistOnDisconnection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Persistence) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Persistence × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Persistence) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Persistence) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Persistence) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Persistence

/-- Self Match Prevention Type: one byte code -/
def SelfMatchPreventionType.codes : List UInt8 :=
  [0x20, 0x31, 0x32, 0x33, 0x34]

inductive SelfMatchPreventionType where
  | naOrDefaultBehaviourAggressiveOrderIsRejected -- Na Or Default Behaviour Aggressive Order Is Rejected
  | rejectAggressiveOrder -- Reject Aggressive Order
  | cancelPasiveOrder -- Cancel Pasive Order
  | cancelBothPassiveAndAggressiveOrder -- Cancel Both Passive And Aggressive Order
  | noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders -- No Order Gets Cancelled Both Aggressive And Passive Orders Remain Only Valid For Spain At Mid Direct Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ SelfMatchPreventionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SelfMatchPreventionType

def toByte : SelfMatchPreventionType → UInt8
  | .naOrDefaultBehaviourAggressiveOrderIsRejected => 0x20
  | .rejectAggressiveOrder => 0x31
  | .cancelPasiveOrder => 0x32
  | .cancelBothPassiveAndAggressiveOrder => 0x33
  | .noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SelfMatchPreventionType :=
  if byte = 0x20 then .naOrDefaultBehaviourAggressiveOrderIsRejected
  else if byte = 0x31 then .rejectAggressiveOrder
  else if byte = 0x32 then .cancelPasiveOrder
  else if byte = 0x33 then .cancelBothPassiveAndAggressiveOrder
  else .noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders

def ofByte (byte : UInt8) : SelfMatchPreventionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SelfMatchPreventionType) : ofByte value.toByte = value := by
  cases value with
  | naOrDefaultBehaviourAggressiveOrderIsRejected => decide
  | rejectAggressiveOrder => decide
  | cancelPasiveOrder => decide
  | cancelBothPassiveAndAggressiveOrder => decide
  | noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SelfMatchPreventionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SelfMatchPreventionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SelfMatchPreventionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SelfMatchPreventionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SelfMatchPreventionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SelfMatchPreventionType

/-- Order Or Quote Cancel: one byte code -/
def OrderOrQuoteCancel.codes : List UInt8 :=
  [0x4E, 0x51, 0x54]

inductive OrderOrQuoteCancel where
  | ordersOnly -- Orders Only
  | quotesOnly -- Quotes Only
  | totalCancellationOrdersAndQuotes -- Total Cancellation Orders And Quotes
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderOrQuoteCancel.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderOrQuoteCancel

def toByte : OrderOrQuoteCancel → UInt8
  | .ordersOnly => 0x4E
  | .quotesOnly => 0x51
  | .totalCancellationOrdersAndQuotes => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderOrQuoteCancel :=
  if byte = 0x4E then .ordersOnly
  else if byte = 0x51 then .quotesOnly
  else .totalCancellationOrdersAndQuotes

def ofByte (byte : UInt8) : OrderOrQuoteCancel :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderOrQuoteCancel) : ofByte value.toByte = value := by
  cases value with
  | ordersOnly => decide
  | quotesOnly => decide
  | totalCancellationOrdersAndQuotes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderOrQuoteCancel) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderOrQuoteCancel × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderOrQuoteCancel) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderOrQuoteCancel) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderOrQuoteCancel) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderOrQuoteCancel

/-- Ord Status: one byte code -/
def OrdStatus.codes : List UInt8 :=
  [0x30, 0x38, 0x31, 0x32, 0x34, 0x50, 0x41, 0x53, 0x43]

inductive OrdStatus where
  | pendingNoVolumeFilled -- Pending No Volume Filled
  | rejected -- Rejected
  | parciallyFilled -- Parcially Filled
  | totallyFilled -- Totally Filled
  | cancelledNotFilled -- Cancelled Not Filled
  | cancelledPartiallyFilled -- Cancelled Partially Filled
  | nonworkingOrderPendingValidation -- Nonworking Order Pending Validation
  | nonworkingOrderPendingActivation -- Nonworking Order Pending Activation
  | expired -- Expired
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdStatus

def toByte : OrdStatus → UInt8
  | .pendingNoVolumeFilled => 0x30
  | .rejected => 0x38
  | .parciallyFilled => 0x31
  | .totallyFilled => 0x32
  | .cancelledNotFilled => 0x34
  | .cancelledPartiallyFilled => 0x50
  | .nonworkingOrderPendingValidation => 0x41
  | .nonworkingOrderPendingActivation => 0x53
  | .expired => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdStatus :=
  if byte = 0x30 then .pendingNoVolumeFilled
  else if byte = 0x38 then .rejected
  else if byte = 0x31 then .parciallyFilled
  else if byte = 0x32 then .totallyFilled
  else if byte = 0x34 then .cancelledNotFilled
  else if byte = 0x50 then .cancelledPartiallyFilled
  else if byte = 0x41 then .nonworkingOrderPendingValidation
  else if byte = 0x53 then .nonworkingOrderPendingActivation
  else .expired

def ofByte (byte : UInt8) : OrdStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdStatus) : ofByte value.toByte = value := by
  cases value with
  | pendingNoVolumeFilled => decide
  | rejected => decide
  | parciallyFilled => decide
  | totallyFilled => decide
  | cancelledNotFilled => decide
  | cancelledPartiallyFilled => decide
  | nonworkingOrderPendingValidation => decide
  | nonworkingOrderPendingActivation => decide
  | expired => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrdStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrdStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdStatus

/-- Ord Rej Reason: one byte code -/
def OrdRejReason.codes : List UInt8 :=
  [0x31, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4F, 0x51, 0x57, 0x58, 0x5A, 0x62, 0x63, 0x64, 0x65, 0x67, 0x68, 0x69, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x78]

inductive OrdRejReason where
  | byTrader -- By Trader
  | bySupervisor -- By Supervisor
  | volumeModificationIncorrectNewVolumeTotalVolumeFilled -- Volume Modification Incorrect New Volume Total Volume Filled
  | notExecutedImmediately -- Not Executed Immediately
  | securityNotCurrentOrNotTradeableForThisMember -- Security Not Current Or Not Tradeable For This Member
  | byLimits -- By Limits
  | cancelledByMarketStatus -- Cancelled By Market Status
  | invalidData -- Invalid Data
  | priceFilters -- Price Filters
  | volumeFilters -- Volume Filters
  | clearingMemberStatus -- Clearing Member Status
  | disconnectionOfTheClientApplication -- Disconnection Of The Client Application
  | quoteParametersMissing -- Quote Parameters Missing
  | byPermissions -- By Permissions
  | quoteOrClOrdIdIncorrect -- Quote Or Cl Ord Id Incorrect
  | deltaProtectionNumberOfContracts -- Delta Protection Number Of Contracts
  | deltaProtectionMaximumAbsoluteDelta -- Delta Protection Maximum Absolute Delta
  | deltaProtectionMximumAccumulateDelta -- Delta Protection Máximum Accumulate Delta
  | byVolatilityAuctionFilters -- By Volatility Auction Filters
  | quoteCancelledBySubstitution -- Quote Cancelled By Substitution
  | notPricesForProcessingTheOrder -- Not Prices For Processing The Order
  | byEndOfValidityOfTheOrder -- By End Of Validity Of The Order
  | other -- Other
  | byMinimumTradingVolume -- By Minimum Trading Volume
  | priceNotAccordingToTheSizeTypology -- Price Not According To The Size Typology
  | theOrderVolumemustBeAMultipleOfTheTradingLotSize -- The Order Volumemust Be A Multiple Of The Trading Lot Size
  | orderRejectedForTriggeringAuction -- Order Rejected For Triggering Auction
  | incorrectPriceOrTriggeredPrice -- Incorrect Price Or Triggered Price
  | incorrectVolume -- Incorrect Volume
  | incorrectDate -- Incorrect Date
  | byContractStatus -- By Contract Status
  | byIntradayFuturesTradingLimit -- By Intraday Futures Trading Limit
  | killButton -- Kill Button
  | byHftFilterLimitMaximumNumberOfContractsMatched -- By Hft Filter Limit Maximum Number Of Contracts Matched
  | bySelfmatchPrevention -- By Selfmatch Prevention
  | auctionPriceOrderCancelledAtTheEndOfTheAuction -- Auction Price Order Cancelled At The End Of The Auction
  | invalidOrkFields -- Invalid Ork Fields
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdRejReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdRejReason

def toByte : OrdRejReason → UInt8
  | .byTrader => 0x31
  | .bySupervisor => 0x33
  | .volumeModificationIncorrectNewVolumeTotalVolumeFilled => 0x34
  | .notExecutedImmediately => 0x35
  | .securityNotCurrentOrNotTradeableForThisMember => 0x36
  | .byLimits => 0x37
  | .cancelledByMarketStatus => 0x38
  | .invalidData => 0x39
  | .priceFilters => 0x42
  | .volumeFilters => 0x43
  | .clearingMemberStatus => 0x44
  | .disconnectionOfTheClientApplication => 0x45
  | .quoteParametersMissing => 0x46
  | .byPermissions => 0x47
  | .quoteOrClOrdIdIncorrect => 0x48
  | .deltaProtectionNumberOfContracts => 0x49
  | .deltaProtectionMaximumAbsoluteDelta => 0x4A
  | .deltaProtectionMximumAccumulateDelta => 0x4B
  | .byVolatilityAuctionFilters => 0x4F
  | .quoteCancelledBySubstitution => 0x51
  | .notPricesForProcessingTheOrder => 0x57
  | .byEndOfValidityOfTheOrder => 0x58
  | .other => 0x5A
  | .byMinimumTradingVolume => 0x62
  | .priceNotAccordingToTheSizeTypology => 0x63
  | .theOrderVolumemustBeAMultipleOfTheTradingLotSize => 0x64
  | .orderRejectedForTriggeringAuction => 0x65
  | .incorrectPriceOrTriggeredPrice => 0x67
  | .incorrectVolume => 0x68
  | .incorrectDate => 0x69
  | .byContractStatus => 0x6B
  | .byIntradayFuturesTradingLimit => 0x6C
  | .killButton => 0x6D
  | .byHftFilterLimitMaximumNumberOfContractsMatched => 0x6E
  | .bySelfmatchPrevention => 0x6F
  | .auctionPriceOrderCancelledAtTheEndOfTheAuction => 0x70
  | .invalidOrkFields => 0x78
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdRejReason :=
  if byte = 0x31 then .byTrader
  else if byte = 0x33 then .bySupervisor
  else if byte = 0x34 then .volumeModificationIncorrectNewVolumeTotalVolumeFilled
  else if byte = 0x35 then .notExecutedImmediately
  else if byte = 0x36 then .securityNotCurrentOrNotTradeableForThisMember
  else if byte = 0x37 then .byLimits
  else if byte = 0x38 then .cancelledByMarketStatus
  else if byte = 0x39 then .invalidData
  else if byte = 0x42 then .priceFilters
  else if byte = 0x43 then .volumeFilters
  else if byte = 0x44 then .clearingMemberStatus
  else if byte = 0x45 then .disconnectionOfTheClientApplication
  else if byte = 0x46 then .quoteParametersMissing
  else if byte = 0x47 then .byPermissions
  else if byte = 0x48 then .quoteOrClOrdIdIncorrect
  else if byte = 0x49 then .deltaProtectionNumberOfContracts
  else if byte = 0x4A then .deltaProtectionMaximumAbsoluteDelta
  else if byte = 0x4B then .deltaProtectionMximumAccumulateDelta
  else if byte = 0x4F then .byVolatilityAuctionFilters
  else if byte = 0x51 then .quoteCancelledBySubstitution
  else if byte = 0x57 then .notPricesForProcessingTheOrder
  else if byte = 0x58 then .byEndOfValidityOfTheOrder
  else if byte = 0x5A then .other
  else if byte = 0x62 then .byMinimumTradingVolume
  else if byte = 0x63 then .priceNotAccordingToTheSizeTypology
  else if byte = 0x64 then .theOrderVolumemustBeAMultipleOfTheTradingLotSize
  else if byte = 0x65 then .orderRejectedForTriggeringAuction
  else if byte = 0x67 then .incorrectPriceOrTriggeredPrice
  else if byte = 0x68 then .incorrectVolume
  else if byte = 0x69 then .incorrectDate
  else if byte = 0x6B then .byContractStatus
  else if byte = 0x6C then .byIntradayFuturesTradingLimit
  else if byte = 0x6D then .killButton
  else if byte = 0x6E then .byHftFilterLimitMaximumNumberOfContractsMatched
  else if byte = 0x6F then .bySelfmatchPrevention
  else if byte = 0x70 then .auctionPriceOrderCancelledAtTheEndOfTheAuction
  else .invalidOrkFields

def ofByte (byte : UInt8) : OrdRejReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdRejReason) : ofByte value.toByte = value := by
  cases value with
  | byTrader => decide
  | bySupervisor => decide
  | volumeModificationIncorrectNewVolumeTotalVolumeFilled => decide
  | notExecutedImmediately => decide
  | securityNotCurrentOrNotTradeableForThisMember => decide
  | byLimits => decide
  | cancelledByMarketStatus => decide
  | invalidData => decide
  | priceFilters => decide
  | volumeFilters => decide
  | clearingMemberStatus => decide
  | disconnectionOfTheClientApplication => decide
  | quoteParametersMissing => decide
  | byPermissions => decide
  | quoteOrClOrdIdIncorrect => decide
  | deltaProtectionNumberOfContracts => decide
  | deltaProtectionMaximumAbsoluteDelta => decide
  | deltaProtectionMximumAccumulateDelta => decide
  | byVolatilityAuctionFilters => decide
  | quoteCancelledBySubstitution => decide
  | notPricesForProcessingTheOrder => decide
  | byEndOfValidityOfTheOrder => decide
  | other => decide
  | byMinimumTradingVolume => decide
  | priceNotAccordingToTheSizeTypology => decide
  | theOrderVolumemustBeAMultipleOfTheTradingLotSize => decide
  | orderRejectedForTriggeringAuction => decide
  | incorrectPriceOrTriggeredPrice => decide
  | incorrectVolume => decide
  | incorrectDate => decide
  | byContractStatus => decide
  | byIntradayFuturesTradingLimit => decide
  | killButton => decide
  | byHftFilterLimitMaximumNumberOfContractsMatched => decide
  | bySelfmatchPrevention => decide
  | auctionPriceOrderCancelledAtTheEndOfTheAuction => decide
  | invalidOrkFields => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdRejReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdRejReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdRejReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrdRejReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrdRejReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdRejReason

/-- Exec Type: one byte code -/
def ExecType.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x4D, 0x47, 0x46, 0x52, 0x44, 0x38, 0x4E, 0x50, 0x56, 0x49, 0x58, 0x57]

inductive ExecType where
  | newOrderConfirmation -- New Order Confirmation
  | orderCancellation -- Order Cancellation
  | orderRefreshDueToChangeOfBook -- Order Refresh Due To Change Of Book
  | orderModification -- Order Modification
  | orderModificationDeletingIntermediatedMember -- Order Modification Deleting Intermediated Member
  | orderModificationChangingIntermediatedMember -- Order Modification Changing Intermediated Member
  | orderRefresh -- Order Refresh
  | stopOrderTriggeredAtthecloseOrderActivation -- Stop Order Triggered Attheclose Order Activation
  | orderRejection -- Order Rejection
  | orderPendingValidation -- Order Pending Validation
  | orderModificationPendingValidation -- Order Modification Pending Validation
  | orderRefreshDueToNewDisplayQty -- Order Refresh Due To New Display Qty
  | beginningOfDayOrderRefresh -- Beginning Of Day Order Refresh
  | expiredOrder -- Expired Order
  | orderStatus -- Order Status
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType

def toByte : ExecType → UInt8
  | .newOrderConfirmation => 0x41
  | .orderCancellation => 0x42
  | .orderRefreshDueToChangeOfBook => 0x43
  | .orderModification => 0x4D
  | .orderModificationDeletingIntermediatedMember => 0x47
  | .orderModificationChangingIntermediatedMember => 0x46
  | .orderRefresh => 0x52
  | .stopOrderTriggeredAtthecloseOrderActivation => 0x44
  | .orderRejection => 0x38
  | .orderPendingValidation => 0x4E
  | .orderModificationPendingValidation => 0x50
  | .orderRefreshDueToNewDisplayQty => 0x56
  | .beginningOfDayOrderRefresh => 0x49
  | .expiredOrder => 0x58
  | .orderStatus => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType :=
  if byte = 0x41 then .newOrderConfirmation
  else if byte = 0x42 then .orderCancellation
  else if byte = 0x43 then .orderRefreshDueToChangeOfBook
  else if byte = 0x4D then .orderModification
  else if byte = 0x47 then .orderModificationDeletingIntermediatedMember
  else if byte = 0x46 then .orderModificationChangingIntermediatedMember
  else if byte = 0x52 then .orderRefresh
  else if byte = 0x44 then .stopOrderTriggeredAtthecloseOrderActivation
  else if byte = 0x38 then .orderRejection
  else if byte = 0x4E then .orderPendingValidation
  else if byte = 0x50 then .orderModificationPendingValidation
  else if byte = 0x56 then .orderRefreshDueToNewDisplayQty
  else if byte = 0x49 then .beginningOfDayOrderRefresh
  else if byte = 0x58 then .expiredOrder
  else .orderStatus

def ofByte (byte : UInt8) : ExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType) : ofByte value.toByte = value := by
  cases value with
  | newOrderConfirmation => decide
  | orderCancellation => decide
  | orderRefreshDueToChangeOfBook => decide
  | orderModification => decide
  | orderModificationDeletingIntermediatedMember => decide
  | orderModificationChangingIntermediatedMember => decide
  | orderRefresh => decide
  | stopOrderTriggeredAtthecloseOrderActivation => decide
  | orderRejection => decide
  | orderPendingValidation => decide
  | orderModificationPendingValidation => decide
  | orderRefreshDueToNewDisplayQty => decide
  | beginningOfDayOrderRefresh => decide
  | expiredOrder => decide
  | orderStatus => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExecType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExecType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecType

/-- Ord Status 2: one byte code -/
def OrdStatus2.codes : List UInt8 :=
  [0x30, 0x38, 0x31, 0x32, 0x34, 0x50, 0x41, 0x53]

inductive OrdStatus2 where
  | pendingNoVolumeFilled -- Pending No Volume Filled
  | rejected -- Rejected
  | parciallyFilled -- Parcially Filled
  | totallyFilled -- Totally Filled
  | cancelledNotFilled -- Cancelled Not Filled
  | cancelledPartiallyFilled -- Cancelled Partially Filled
  | nonworkingOrderPendingValidation -- Nonworking Order Pending Validation
  | nonworkingOrderPendingActivation -- Nonworking Order Pending Activation
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdStatus2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdStatus2

def toByte : OrdStatus2 → UInt8
  | .pendingNoVolumeFilled => 0x30
  | .rejected => 0x38
  | .parciallyFilled => 0x31
  | .totallyFilled => 0x32
  | .cancelledNotFilled => 0x34
  | .cancelledPartiallyFilled => 0x50
  | .nonworkingOrderPendingValidation => 0x41
  | .nonworkingOrderPendingActivation => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdStatus2 :=
  if byte = 0x30 then .pendingNoVolumeFilled
  else if byte = 0x38 then .rejected
  else if byte = 0x31 then .parciallyFilled
  else if byte = 0x32 then .totallyFilled
  else if byte = 0x34 then .cancelledNotFilled
  else if byte = 0x50 then .cancelledPartiallyFilled
  else if byte = 0x41 then .nonworkingOrderPendingValidation
  else .nonworkingOrderPendingActivation

def ofByte (byte : UInt8) : OrdStatus2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdStatus2) : ofByte value.toByte = value := by
  cases value with
  | pendingNoVolumeFilled => decide
  | rejected => decide
  | parciallyFilled => decide
  | totallyFilled => decide
  | cancelledNotFilled => decide
  | cancelledPartiallyFilled => decide
  | nonworkingOrderPendingValidation => decide
  | nonworkingOrderPendingActivation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdStatus2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdStatus2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdStatus2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrdStatus2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrdStatus2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdStatus2

/-- Ord Rej Reason 2: one byte code -/
def OrdRejReason2.codes : List UInt8 :=
  [0x31, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4F, 0x51, 0x57, 0x58, 0x5A, 0x62, 0x63, 0x64, 0x65, 0x67, 0x68, 0x69, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x78]

inductive OrdRejReason2 where
  | byTrader -- By Trader
  | bySupervisor -- By Supervisor
  | volumeModificationIncorrectNewVolumeTotalVolumeFilled -- Volume Modification Incorrect New Volume Total Volume Filled
  | notExecutedImmediately -- Not Executed Immediately
  | securityNotCurrentOrNotTradeableForThisMember -- Security Not Current Or Not Tradeable For This Member
  | byLimits -- By Limits
  | cancelledByMarketStatus -- Cancelled By Market Status
  | invalidData -- Invalid Data
  | priceFilters -- Price Filters
  | volumeFilters -- Volume Filters
  | clearingMemberStatus -- Clearing Member Status
  | disconnectionOfTheClientApplication -- Disconnection Of The Client Application
  | quoteParametersMissing -- Quote Parameters Missing
  | byPermissions -- By Permissions
  | quoteOrClOrdIdIncorrect -- Quote Or Cl Ord Id Incorrect
  | deltaProtectionNumberOfContracts -- Delta Protection Number Of Contracts
  | deltaProtectionMaximumAbsoluteDelta -- Delta Protection Maximum Absolute Delta
  | deltaProtectionMximumAccumulateDelta -- Delta Protection Máximum Accumulate Delta
  | byVolatilityAuctionFilters -- By Volatility Auction Filters
  | quoteCancelledBySubstitution -- Quote Cancelled By Substitution
  | notPricesForProcessingTheOrder -- Not Prices For Processing The Order
  | byEndOfValidityOfTheOrder -- By End Of Validity Of The Order
  | other -- Other
  | byMinimumTradingVolume -- By Minimum Trading Volume
  | priceNotAccordingToTheSizeTypology -- Price Not According To The Size Typology
  | theOrderVolumemustBeAMultipleOfTheTradingLotSize -- The Order Volumemust Be A Multiple Of The Trading Lot Size
  | orderRejectedForTriggeringAuction -- Order Rejected For Triggering Auction
  | incorrectPriceOrTriggeredPrice -- Incorrect Price Or Triggered Price
  | incorrectVolume -- Incorrect Volume
  | incorrectDate -- Incorrect Date
  | byContractStatus -- By Contract Status
  | byIntradayFuturesTradingLimit -- By Intraday Futures Trading Limit
  | killButton -- Kill Button
  | byHftFilterLimitMaximumNumberOfContractsMatched -- By Hft Filter Limit Maximum Number Of Contracts Matched
  | bySelfmatchPrevention -- By Selfmatch Prevention
  | auctionPriceOrderCancelledAtTheEndOfTheAuction -- Auction Price Order Cancelled At The End Of The Auction
  | invalidOrkFields -- Invalid Ork Fields
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdRejReason2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdRejReason2

def toByte : OrdRejReason2 → UInt8
  | .byTrader => 0x31
  | .bySupervisor => 0x33
  | .volumeModificationIncorrectNewVolumeTotalVolumeFilled => 0x34
  | .notExecutedImmediately => 0x35
  | .securityNotCurrentOrNotTradeableForThisMember => 0x36
  | .byLimits => 0x37
  | .cancelledByMarketStatus => 0x38
  | .invalidData => 0x39
  | .priceFilters => 0x42
  | .volumeFilters => 0x43
  | .clearingMemberStatus => 0x44
  | .disconnectionOfTheClientApplication => 0x45
  | .quoteParametersMissing => 0x46
  | .byPermissions => 0x47
  | .quoteOrClOrdIdIncorrect => 0x48
  | .deltaProtectionNumberOfContracts => 0x49
  | .deltaProtectionMaximumAbsoluteDelta => 0x4A
  | .deltaProtectionMximumAccumulateDelta => 0x4B
  | .byVolatilityAuctionFilters => 0x4F
  | .quoteCancelledBySubstitution => 0x51
  | .notPricesForProcessingTheOrder => 0x57
  | .byEndOfValidityOfTheOrder => 0x58
  | .other => 0x5A
  | .byMinimumTradingVolume => 0x62
  | .priceNotAccordingToTheSizeTypology => 0x63
  | .theOrderVolumemustBeAMultipleOfTheTradingLotSize => 0x64
  | .orderRejectedForTriggeringAuction => 0x65
  | .incorrectPriceOrTriggeredPrice => 0x67
  | .incorrectVolume => 0x68
  | .incorrectDate => 0x69
  | .byContractStatus => 0x6B
  | .byIntradayFuturesTradingLimit => 0x6C
  | .killButton => 0x6D
  | .byHftFilterLimitMaximumNumberOfContractsMatched => 0x6E
  | .bySelfmatchPrevention => 0x6F
  | .auctionPriceOrderCancelledAtTheEndOfTheAuction => 0x70
  | .invalidOrkFields => 0x78
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdRejReason2 :=
  if byte = 0x31 then .byTrader
  else if byte = 0x33 then .bySupervisor
  else if byte = 0x34 then .volumeModificationIncorrectNewVolumeTotalVolumeFilled
  else if byte = 0x35 then .notExecutedImmediately
  else if byte = 0x36 then .securityNotCurrentOrNotTradeableForThisMember
  else if byte = 0x37 then .byLimits
  else if byte = 0x38 then .cancelledByMarketStatus
  else if byte = 0x39 then .invalidData
  else if byte = 0x42 then .priceFilters
  else if byte = 0x43 then .volumeFilters
  else if byte = 0x44 then .clearingMemberStatus
  else if byte = 0x45 then .disconnectionOfTheClientApplication
  else if byte = 0x46 then .quoteParametersMissing
  else if byte = 0x47 then .byPermissions
  else if byte = 0x48 then .quoteOrClOrdIdIncorrect
  else if byte = 0x49 then .deltaProtectionNumberOfContracts
  else if byte = 0x4A then .deltaProtectionMaximumAbsoluteDelta
  else if byte = 0x4B then .deltaProtectionMximumAccumulateDelta
  else if byte = 0x4F then .byVolatilityAuctionFilters
  else if byte = 0x51 then .quoteCancelledBySubstitution
  else if byte = 0x57 then .notPricesForProcessingTheOrder
  else if byte = 0x58 then .byEndOfValidityOfTheOrder
  else if byte = 0x5A then .other
  else if byte = 0x62 then .byMinimumTradingVolume
  else if byte = 0x63 then .priceNotAccordingToTheSizeTypology
  else if byte = 0x64 then .theOrderVolumemustBeAMultipleOfTheTradingLotSize
  else if byte = 0x65 then .orderRejectedForTriggeringAuction
  else if byte = 0x67 then .incorrectPriceOrTriggeredPrice
  else if byte = 0x68 then .incorrectVolume
  else if byte = 0x69 then .incorrectDate
  else if byte = 0x6B then .byContractStatus
  else if byte = 0x6C then .byIntradayFuturesTradingLimit
  else if byte = 0x6D then .killButton
  else if byte = 0x6E then .byHftFilterLimitMaximumNumberOfContractsMatched
  else if byte = 0x6F then .bySelfmatchPrevention
  else if byte = 0x70 then .auctionPriceOrderCancelledAtTheEndOfTheAuction
  else .invalidOrkFields

def ofByte (byte : UInt8) : OrdRejReason2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdRejReason2) : ofByte value.toByte = value := by
  cases value with
  | byTrader => decide
  | bySupervisor => decide
  | volumeModificationIncorrectNewVolumeTotalVolumeFilled => decide
  | notExecutedImmediately => decide
  | securityNotCurrentOrNotTradeableForThisMember => decide
  | byLimits => decide
  | cancelledByMarketStatus => decide
  | invalidData => decide
  | priceFilters => decide
  | volumeFilters => decide
  | clearingMemberStatus => decide
  | disconnectionOfTheClientApplication => decide
  | quoteParametersMissing => decide
  | byPermissions => decide
  | quoteOrClOrdIdIncorrect => decide
  | deltaProtectionNumberOfContracts => decide
  | deltaProtectionMaximumAbsoluteDelta => decide
  | deltaProtectionMximumAccumulateDelta => decide
  | byVolatilityAuctionFilters => decide
  | quoteCancelledBySubstitution => decide
  | notPricesForProcessingTheOrder => decide
  | byEndOfValidityOfTheOrder => decide
  | other => decide
  | byMinimumTradingVolume => decide
  | priceNotAccordingToTheSizeTypology => decide
  | theOrderVolumemustBeAMultipleOfTheTradingLotSize => decide
  | orderRejectedForTriggeringAuction => decide
  | incorrectPriceOrTriggeredPrice => decide
  | incorrectVolume => decide
  | incorrectDate => decide
  | byContractStatus => decide
  | byIntradayFuturesTradingLimit => decide
  | killButton => decide
  | byHftFilterLimitMaximumNumberOfContractsMatched => decide
  | bySelfmatchPrevention => decide
  | auctionPriceOrderCancelledAtTheEndOfTheAuction => decide
  | invalidOrkFields => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdRejReason2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdRejReason2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdRejReason2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrdRejReason2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrdRejReason2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdRejReason2

/-- Exec Type 2: one byte code -/
def ExecType2.codes : List UInt8 :=
  [0x41, 0x42, 0x4D, 0x52, 0x38, 0x58, 0x57]

inductive ExecType2 where
  | newOrderConfirmation -- New Order Confirmation
  | orderCancellation -- Order Cancellation
  | orderModification -- Order Modification
  | orderRefresh -- Order Refresh
  | orderRejection -- Order Rejection
  | expiredOrder -- Expired Order
  | orderStatus -- Order Status
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType2

def toByte : ExecType2 → UInt8
  | .newOrderConfirmation => 0x41
  | .orderCancellation => 0x42
  | .orderModification => 0x4D
  | .orderRefresh => 0x52
  | .orderRejection => 0x38
  | .expiredOrder => 0x58
  | .orderStatus => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType2 :=
  if byte = 0x41 then .newOrderConfirmation
  else if byte = 0x42 then .orderCancellation
  else if byte = 0x4D then .orderModification
  else if byte = 0x52 then .orderRefresh
  else if byte = 0x38 then .orderRejection
  else if byte = 0x58 then .expiredOrder
  else .orderStatus

def ofByte (byte : UInt8) : ExecType2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType2) : ofByte value.toByte = value := by
  cases value with
  | newOrderConfirmation => decide
  | orderCancellation => decide
  | orderModification => decide
  | orderRefresh => decide
  | orderRejection => decide
  | expiredOrder => decide
  | orderStatus => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecType2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecType2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecType2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExecType2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExecType2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecType2

/-- Cxl Rej Response To: one byte code -/
def CxlRejResponseTo.codes : List UInt8 :=
  [0x31, 0x32]

inductive CxlRejResponseTo where
  | simpleOrderModification -- Simple Order Modification
  | orderCancellationRequest -- Order Cancellation Request
  | unlisted (byte : { byte : UInt8 // byte ∉ CxlRejResponseTo.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CxlRejResponseTo

def toByte : CxlRejResponseTo → UInt8
  | .simpleOrderModification => 0x31
  | .orderCancellationRequest => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CxlRejResponseTo :=
  if byte = 0x31 then .simpleOrderModification
  else .orderCancellationRequest

def ofByte (byte : UInt8) : CxlRejResponseTo :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CxlRejResponseTo) : ofByte value.toByte = value := by
  cases value with
  | simpleOrderModification => decide
  | orderCancellationRequest => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CxlRejResponseTo) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CxlRejResponseTo × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CxlRejResponseTo) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CxlRejResponseTo) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CxlRejResponseTo) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CxlRejResponseTo

/-- Cxl Rej Reason: one byte code -/
def CxlRejReason.codes : List UInt8 :=
  [0x31, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4F, 0x51, 0x57, 0x58, 0x5A, 0x62, 0x63, 0x64, 0x65, 0x67, 0x68, 0x69, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x78]

inductive CxlRejReason where
  | byTrader -- By Trader
  | bySupervisor -- By Supervisor
  | volumeModificationIncorrectNewVolumeTotalVolumeFilled -- Volume Modification Incorrect New Volume Total Volume Filled
  | notExecutedImmediately -- Not Executed Immediately
  | securityNotCurrentOrNotTradeableForThisMember -- Security Not Current Or Not Tradeable For This Member
  | byLimits -- By Limits
  | cancelledByMarketStatus -- Cancelled By Market Status
  | invalidData -- Invalid Data
  | priceFilters -- Price Filters
  | volumeFilters -- Volume Filters
  | clearingMemberStatus -- Clearing Member Status
  | disconnectionOfTheClientApplication -- Disconnection Of The Client Application
  | quoteParametersMissing -- Quote Parameters Missing
  | byPermissions -- By Permissions
  | quoteOrClOrdIdIncorrect -- Quote Or Cl Ord Id Incorrect
  | deltaProtectionNumberOfContracts -- Delta Protection Number Of Contracts
  | deltaProtectionMaximumAbsoluteDelta -- Delta Protection Maximum Absolute Delta
  | deltaProtectionMximumAccumulateDelta -- Delta Protection Máximum Accumulate Delta
  | byVolatilityAuctionFilters -- By Volatility Auction Filters
  | quoteCancelledBySubstitution -- Quote Cancelled By Substitution
  | notPricesForProcessingTheOrder -- Not Prices For Processing The Order
  | byEndOfValidityOfTheOrder -- By End Of Validity Of The Order
  | other -- Other
  | byMinimumTradingVolume -- By Minimum Trading Volume
  | priceNotAccordingToTheSizeTypology -- Price Not According To The Size Typology
  | theOrderVolumemustBeAMultipleOfTheTradingLotSize -- The Order Volumemust Be A Multiple Of The Trading Lot Size
  | orderRejectedForTriggeringAuction -- Order Rejected For Triggering Auction
  | incorrectPriceOrTriggeredPrice -- Incorrect Price Or Triggered Price
  | incorrectVolume -- Incorrect Volume
  | incorrectDate -- Incorrect Date
  | byContractStatus -- By Contract Status
  | byIntradayFuturesTradingLimit -- By Intraday Futures Trading Limit
  | killButton -- Kill Button
  | byHftFilterLimitMaximumNumberOfContractsMatched -- By Hft Filter Limit Maximum Number Of Contracts Matched
  | bySelfmatchPrevention -- By Selfmatch Prevention
  | auctionPriceOrderCancelledAtTheEndOfTheAuction -- Auction Price Order Cancelled At The End Of The Auction
  | invalidOrkFields -- Invalid Ork Fields
  | unlisted (byte : { byte : UInt8 // byte ∉ CxlRejReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CxlRejReason

def toByte : CxlRejReason → UInt8
  | .byTrader => 0x31
  | .bySupervisor => 0x33
  | .volumeModificationIncorrectNewVolumeTotalVolumeFilled => 0x34
  | .notExecutedImmediately => 0x35
  | .securityNotCurrentOrNotTradeableForThisMember => 0x36
  | .byLimits => 0x37
  | .cancelledByMarketStatus => 0x38
  | .invalidData => 0x39
  | .priceFilters => 0x42
  | .volumeFilters => 0x43
  | .clearingMemberStatus => 0x44
  | .disconnectionOfTheClientApplication => 0x45
  | .quoteParametersMissing => 0x46
  | .byPermissions => 0x47
  | .quoteOrClOrdIdIncorrect => 0x48
  | .deltaProtectionNumberOfContracts => 0x49
  | .deltaProtectionMaximumAbsoluteDelta => 0x4A
  | .deltaProtectionMximumAccumulateDelta => 0x4B
  | .byVolatilityAuctionFilters => 0x4F
  | .quoteCancelledBySubstitution => 0x51
  | .notPricesForProcessingTheOrder => 0x57
  | .byEndOfValidityOfTheOrder => 0x58
  | .other => 0x5A
  | .byMinimumTradingVolume => 0x62
  | .priceNotAccordingToTheSizeTypology => 0x63
  | .theOrderVolumemustBeAMultipleOfTheTradingLotSize => 0x64
  | .orderRejectedForTriggeringAuction => 0x65
  | .incorrectPriceOrTriggeredPrice => 0x67
  | .incorrectVolume => 0x68
  | .incorrectDate => 0x69
  | .byContractStatus => 0x6B
  | .byIntradayFuturesTradingLimit => 0x6C
  | .killButton => 0x6D
  | .byHftFilterLimitMaximumNumberOfContractsMatched => 0x6E
  | .bySelfmatchPrevention => 0x6F
  | .auctionPriceOrderCancelledAtTheEndOfTheAuction => 0x70
  | .invalidOrkFields => 0x78
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CxlRejReason :=
  if byte = 0x31 then .byTrader
  else if byte = 0x33 then .bySupervisor
  else if byte = 0x34 then .volumeModificationIncorrectNewVolumeTotalVolumeFilled
  else if byte = 0x35 then .notExecutedImmediately
  else if byte = 0x36 then .securityNotCurrentOrNotTradeableForThisMember
  else if byte = 0x37 then .byLimits
  else if byte = 0x38 then .cancelledByMarketStatus
  else if byte = 0x39 then .invalidData
  else if byte = 0x42 then .priceFilters
  else if byte = 0x43 then .volumeFilters
  else if byte = 0x44 then .clearingMemberStatus
  else if byte = 0x45 then .disconnectionOfTheClientApplication
  else if byte = 0x46 then .quoteParametersMissing
  else if byte = 0x47 then .byPermissions
  else if byte = 0x48 then .quoteOrClOrdIdIncorrect
  else if byte = 0x49 then .deltaProtectionNumberOfContracts
  else if byte = 0x4A then .deltaProtectionMaximumAbsoluteDelta
  else if byte = 0x4B then .deltaProtectionMximumAccumulateDelta
  else if byte = 0x4F then .byVolatilityAuctionFilters
  else if byte = 0x51 then .quoteCancelledBySubstitution
  else if byte = 0x57 then .notPricesForProcessingTheOrder
  else if byte = 0x58 then .byEndOfValidityOfTheOrder
  else if byte = 0x5A then .other
  else if byte = 0x62 then .byMinimumTradingVolume
  else if byte = 0x63 then .priceNotAccordingToTheSizeTypology
  else if byte = 0x64 then .theOrderVolumemustBeAMultipleOfTheTradingLotSize
  else if byte = 0x65 then .orderRejectedForTriggeringAuction
  else if byte = 0x67 then .incorrectPriceOrTriggeredPrice
  else if byte = 0x68 then .incorrectVolume
  else if byte = 0x69 then .incorrectDate
  else if byte = 0x6B then .byContractStatus
  else if byte = 0x6C then .byIntradayFuturesTradingLimit
  else if byte = 0x6D then .killButton
  else if byte = 0x6E then .byHftFilterLimitMaximumNumberOfContractsMatched
  else if byte = 0x6F then .bySelfmatchPrevention
  else if byte = 0x70 then .auctionPriceOrderCancelledAtTheEndOfTheAuction
  else .invalidOrkFields

def ofByte (byte : UInt8) : CxlRejReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CxlRejReason) : ofByte value.toByte = value := by
  cases value with
  | byTrader => decide
  | bySupervisor => decide
  | volumeModificationIncorrectNewVolumeTotalVolumeFilled => decide
  | notExecutedImmediately => decide
  | securityNotCurrentOrNotTradeableForThisMember => decide
  | byLimits => decide
  | cancelledByMarketStatus => decide
  | invalidData => decide
  | priceFilters => decide
  | volumeFilters => decide
  | clearingMemberStatus => decide
  | disconnectionOfTheClientApplication => decide
  | quoteParametersMissing => decide
  | byPermissions => decide
  | quoteOrClOrdIdIncorrect => decide
  | deltaProtectionNumberOfContracts => decide
  | deltaProtectionMaximumAbsoluteDelta => decide
  | deltaProtectionMximumAccumulateDelta => decide
  | byVolatilityAuctionFilters => decide
  | quoteCancelledBySubstitution => decide
  | notPricesForProcessingTheOrder => decide
  | byEndOfValidityOfTheOrder => decide
  | other => decide
  | byMinimumTradingVolume => decide
  | priceNotAccordingToTheSizeTypology => decide
  | theOrderVolumemustBeAMultipleOfTheTradingLotSize => decide
  | orderRejectedForTriggeringAuction => decide
  | incorrectPriceOrTriggeredPrice => decide
  | incorrectVolume => decide
  | incorrectDate => decide
  | byContractStatus => decide
  | byIntradayFuturesTradingLimit => decide
  | killButton => decide
  | byHftFilterLimitMaximumNumberOfContractsMatched => decide
  | bySelfmatchPrevention => decide
  | auctionPriceOrderCancelledAtTheEndOfTheAuction => decide
  | invalidOrkFields => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CxlRejReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CxlRejReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CxlRejReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CxlRejReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CxlRejReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CxlRejReason

/-- Mass Cancel Reject Reason: one byte code -/
def MassCancelRejectReason.codes : List UInt8 :=
  [0x47, 0x38, 0x39]

inductive MassCancelRejectReason where
  | noPermission -- No Permission
  | cancelledBecauseOfMarketState -- Cancelled Because Of Market State
  | invalidData -- Invalid Data
  | unlisted (byte : { byte : UInt8 // byte ∉ MassCancelRejectReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MassCancelRejectReason

def toByte : MassCancelRejectReason → UInt8
  | .noPermission => 0x47
  | .cancelledBecauseOfMarketState => 0x38
  | .invalidData => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MassCancelRejectReason :=
  if byte = 0x47 then .noPermission
  else if byte = 0x38 then .cancelledBecauseOfMarketState
  else .invalidData

def ofByte (byte : UInt8) : MassCancelRejectReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MassCancelRejectReason) : ofByte value.toByte = value := by
  cases value with
  | noPermission => decide
  | cancelledBecauseOfMarketState => decide
  | invalidData => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MassCancelRejectReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MassCancelRejectReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MassCancelRejectReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MassCancelRejectReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MassCancelRejectReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MassCancelRejectReason

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x48, 0x4C, 0x4D, 0x52, 0x53, 0x57, 0x58, 0x33, 0x34, 0x36, 0x38, 0x39]

inductive TradeType where
  | crossTradeDuringTradingHours -- Cross Trade During Trading Hours
  | delta -- Delta
  | market -- Market
  | strategyTradesTimeSpreadFuturesAndStrategies -- Strategy Trades Time Spread Futures And Strategies
  | componentsOfTradeR -- Components Of Trade R
  | tradeAmendment -- Trade Amendment
  | countertrade -- Countertrade
  | rfq -- Rfq
  | rfqXRolling -- Rfq X Rolling
  | rfqXRollingDuringAuction -- Rfq X Rolling During Auction
  | rfqXRollingAmendment -- Rfq X Rolling Amendment
  | rfqXRollingDuringAuctionAmendment -- Rfq X Rolling During Auction Amendment
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .crossTradeDuringTradingHours => 0x48
  | .delta => 0x4C
  | .market => 0x4D
  | .strategyTradesTimeSpreadFuturesAndStrategies => 0x52
  | .componentsOfTradeR => 0x53
  | .tradeAmendment => 0x57
  | .countertrade => 0x58
  | .rfq => 0x33
  | .rfqXRolling => 0x34
  | .rfqXRollingDuringAuction => 0x36
  | .rfqXRollingAmendment => 0x38
  | .rfqXRollingDuringAuctionAmendment => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x48 then .crossTradeDuringTradingHours
  else if byte = 0x4C then .delta
  else if byte = 0x4D then .market
  else if byte = 0x52 then .strategyTradesTimeSpreadFuturesAndStrategies
  else if byte = 0x53 then .componentsOfTradeR
  else if byte = 0x57 then .tradeAmendment
  else if byte = 0x58 then .countertrade
  else if byte = 0x33 then .rfq
  else if byte = 0x34 then .rfqXRolling
  else if byte = 0x36 then .rfqXRollingDuringAuction
  else if byte = 0x38 then .rfqXRollingAmendment
  else .rfqXRollingDuringAuctionAmendment

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | crossTradeDuringTradingHours => decide
  | delta => decide
  | market => decide
  | strategyTradesTimeSpreadFuturesAndStrategies => decide
  | componentsOfTradeR => decide
  | tradeAmendment => decide
  | countertrade => decide
  | rfq => decide
  | rfqXRolling => decide
  | rfqXRollingDuringAuction => decide
  | rfqXRollingAmendment => decide
  | rfqXRollingDuringAuctionAmendment => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeType

/-- Designation: one byte code -/
def Designation.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x43]

inductive Designation where
  | tradeDuringOpenMarket -- Trade During Open Market
  | tradeDuringOpeningAuction -- Trade During Opening Auction
  | tradeDuringClosingAuction -- Trade During Closing Auction
  | tradeDuringVolatilityAuction -- Trade During Volatility Auction
  | tradeDuringManualAuction -- Trade During Manual Auction
  | tradeDuringOpeningAuctionExtension -- Trade During Opening Auction Extension
  | tradeDuringClosingAuctionExtension -- Trade During Closing Auction Extension
  | tradeDuringTalPeriod -- Trade During Tal Period
  | tradeInSpainAtMidDarkBook -- Trade In Spain At Mid Dark Book
  | unlisted (byte : { byte : UInt8 // byte ∉ Designation.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Designation

def toByte : Designation → UInt8
  | .tradeDuringOpenMarket => 0x31
  | .tradeDuringOpeningAuction => 0x32
  | .tradeDuringClosingAuction => 0x33
  | .tradeDuringVolatilityAuction => 0x34
  | .tradeDuringManualAuction => 0x35
  | .tradeDuringOpeningAuctionExtension => 0x36
  | .tradeDuringClosingAuctionExtension => 0x37
  | .tradeDuringTalPeriod => 0x38
  | .tradeInSpainAtMidDarkBook => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Designation :=
  if byte = 0x31 then .tradeDuringOpenMarket
  else if byte = 0x32 then .tradeDuringOpeningAuction
  else if byte = 0x33 then .tradeDuringClosingAuction
  else if byte = 0x34 then .tradeDuringVolatilityAuction
  else if byte = 0x35 then .tradeDuringManualAuction
  else if byte = 0x36 then .tradeDuringOpeningAuctionExtension
  else if byte = 0x37 then .tradeDuringClosingAuctionExtension
  else if byte = 0x38 then .tradeDuringTalPeriod
  else .tradeInSpainAtMidDarkBook

def ofByte (byte : UInt8) : Designation :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Designation) : ofByte value.toByte = value := by
  cases value with
  | tradeDuringOpenMarket => decide
  | tradeDuringOpeningAuction => decide
  | tradeDuringClosingAuction => decide
  | tradeDuringVolatilityAuction => decide
  | tradeDuringManualAuction => decide
  | tradeDuringOpeningAuctionExtension => decide
  | tradeDuringClosingAuctionExtension => decide
  | tradeDuringTalPeriod => decide
  | tradeInSpainAtMidDarkBook => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Designation) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Designation × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Designation) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Designation) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Designation) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Designation

/-- Market Mechanism: one byte code -/
def MarketMechanism.codes : List UInt8 :=
  [0x30, 0x31, 0x36]

inductive MarketMechanism where
  | centralLimitOrderBook -- Central Limit Order Book
  | offBookMessagingTrading -- Off Book Messaging Trading
  | requestForQuotes -- Request For Quotes
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketMechanism.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketMechanism

def toByte : MarketMechanism → UInt8
  | .centralLimitOrderBook => 0x30
  | .offBookMessagingTrading => 0x31
  | .requestForQuotes => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketMechanism :=
  if byte = 0x30 then .centralLimitOrderBook
  else if byte = 0x31 then .offBookMessagingTrading
  else .requestForQuotes

def ofByte (byte : UInt8) : MarketMechanism :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketMechanism) : ofByte value.toByte = value := by
  cases value with
  | centralLimitOrderBook => decide
  | offBookMessagingTrading => decide
  | requestForQuotes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketMechanism) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketMechanism × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketMechanism) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketMechanism) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketMechanism) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketMechanism

/-- Transaction Category: one byte code -/
def TransactionCategory.codes : List UInt8 :=
  [0x20, 0x59, 0x5A]

inductive TransactionCategory where
  | normalCategory -- Normal Category
  | exchangeForPhysicalsXfph -- Exchange For Physicals Xfph
  | packageTradeExcludingExchangeForPhysicalsTpac -- Package Trade Excluding Exchange For Physicals Tpac
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionCategory

def toByte : TransactionCategory → UInt8
  | .normalCategory => 0x20
  | .exchangeForPhysicalsXfph => 0x59
  | .packageTradeExcludingExchangeForPhysicalsTpac => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionCategory :=
  if byte = 0x20 then .normalCategory
  else if byte = 0x59 then .exchangeForPhysicalsXfph
  else .packageTradeExcludingExchangeForPhysicalsTpac

def ofByte (byte : UInt8) : TransactionCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionCategory) : ofByte value.toByte = value := by
  cases value with
  | normalCategory => decide
  | exchangeForPhysicalsXfph => decide
  | packageTradeExcludingExchangeForPhysicalsTpac => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionCategory) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TransactionCategory) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TransactionCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionCategory

/-- Ccp Code: one byte code -/
def CcpCode.codes : List UInt8 :=
  [0x30, 0x31]

inductive CcpCode where
  | na -- Na
  | bmeClearingOthersToBeDefined -- Bme Clearing… Others To Be Defined
  | unlisted (byte : { byte : UInt8 // byte ∉ CcpCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CcpCode

def toByte : CcpCode → UInt8
  | .na => 0x30
  | .bmeClearingOthersToBeDefined => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CcpCode :=
  if byte = 0x30 then .na
  else .bmeClearingOthersToBeDefined

def ofByte (byte : UInt8) : CcpCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CcpCode) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | bmeClearingOthersToBeDefined => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CcpCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CcpCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CcpCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CcpCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CcpCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CcpCode

/-- Aggressor Indicator: one byte code -/
def AggressorIndicator.codes : List UInt8 :=
  [0x20, 0x50, 0x41]

inductive AggressorIndicator where
  | na -- Na
  | passive -- Passive
  | aggresive -- Aggresive
  | unlisted (byte : { byte : UInt8 // byte ∉ AggressorIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AggressorIndicator

def toByte : AggressorIndicator → UInt8
  | .na => 0x20
  | .passive => 0x50
  | .aggresive => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AggressorIndicator :=
  if byte = 0x20 then .na
  else if byte = 0x50 then .passive
  else .aggresive

def ofByte (byte : UInt8) : AggressorIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AggressorIndicator) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | passive => decide
  | aggresive => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AggressorIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AggressorIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AggressorIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AggressorIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AggressorIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AggressorIndicator

/-- Ccp Code 2: one byte code -/
def CcpCode2.codes : List UInt8 :=
  [0x30, 0x31]

inductive CcpCode2 where
  | na -- Na
  | bmeClearingOthersToBeDefined -- Bme Clearing… Others To Be Defined
  | unlisted (byte : { byte : UInt8 // byte ∉ CcpCode2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CcpCode2

def toByte : CcpCode2 → UInt8
  | .na => 0x30
  | .bmeClearingOthersToBeDefined => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CcpCode2 :=
  if byte = 0x30 then .na
  else .bmeClearingOthersToBeDefined

def ofByte (byte : UInt8) : CcpCode2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CcpCode2) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | bmeClearingOthersToBeDefined => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CcpCode2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CcpCode2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CcpCode2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CcpCode2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CcpCode2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CcpCode2

/-- Aggressor Indicator 2: one byte code -/
def AggressorIndicator2.codes : List UInt8 :=
  [0x20, 0x50, 0x41]

inductive AggressorIndicator2 where
  | na -- Na
  | passive -- Passive
  | aggressive -- Aggressive
  | unlisted (byte : { byte : UInt8 // byte ∉ AggressorIndicator2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AggressorIndicator2

def toByte : AggressorIndicator2 → UInt8
  | .na => 0x20
  | .passive => 0x50
  | .aggressive => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AggressorIndicator2 :=
  if byte = 0x20 then .na
  else if byte = 0x50 then .passive
  else .aggressive

def ofByte (byte : UInt8) : AggressorIndicator2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AggressorIndicator2) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | passive => decide
  | aggressive => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AggressorIndicator2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AggressorIndicator2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AggressorIndicator2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AggressorIndicator2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AggressorIndicator2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AggressorIndicator2

/-- Bencrfpt Flag: one byte code -/
def BencrfptFlag.codes : List UInt8 :=
  [0x20, 0x36]

inductive BencrfptFlag where
  | normalTrade -- Normal Trade
  | benchmarkTradeBenc -- Benchmark Trade Benc
  | unlisted (byte : { byte : UInt8 // byte ∉ BencrfptFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BencrfptFlag

def toByte : BencrfptFlag → UInt8
  | .normalTrade => 0x20
  | .benchmarkTradeBenc => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BencrfptFlag :=
  if byte = 0x20 then .normalTrade
  else .benchmarkTradeBenc

def ofByte (byte : UInt8) : BencrfptFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BencrfptFlag) : ofByte value.toByte = value := by
  cases value with
  | normalTrade => decide
  | benchmarkTradeBenc => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BencrfptFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BencrfptFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BencrfptFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BencrfptFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BencrfptFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BencrfptFlag

/-- Trade Price Condition: one byte code -/
def TradePriceCondition.codes : List UInt8 :=
  [0x20, 0x35]

inductive TradePriceCondition where
  | plainVanillaTrade -- Plain Vanilla Trade
  | nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft -- Non Price Forming Trade Formerly Defined As A Technical Trade Npft
  | unlisted (byte : { byte : UInt8 // byte ∉ TradePriceCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradePriceCondition

def toByte : TradePriceCondition → UInt8
  | .plainVanillaTrade => 0x20
  | .nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradePriceCondition :=
  if byte = 0x20 then .plainVanillaTrade
  else .nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft

def ofByte (byte : UInt8) : TradePriceCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradePriceCondition) : ofByte value.toByte = value := by
  cases value with
  | plainVanillaTrade => decide
  | nonPriceFormingTradeFormerlyDefinedAsATechnicalTradeNpft => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradePriceCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradePriceCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradePriceCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradePriceCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradePriceCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradePriceCondition

/-- Pre Trade Transparency Waiver: one byte code -/
def PreTradeTransparencyWaiver.codes : List UInt8 :=
  [0x20]

inductive PreTradeTransparencyWaiver where
  | negotiatedTradeNego -- Negotiated Trade Nego
  | unlisted (byte : { byte : UInt8 // byte ∉ PreTradeTransparencyWaiver.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PreTradeTransparencyWaiver

def toByte : PreTradeTransparencyWaiver → UInt8
  | .negotiatedTradeNego => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : PreTradeTransparencyWaiver :=
  .negotiatedTradeNego

def ofByte (byte : UInt8) : PreTradeTransparencyWaiver :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PreTradeTransparencyWaiver) : ofByte value.toByte = value := by
  cases value with
  | negotiatedTradeNego => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PreTradeTransparencyWaiver) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PreTradeTransparencyWaiver × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PreTradeTransparencyWaiver) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PreTradeTransparencyWaiver) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PreTradeTransparencyWaiver) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PreTradeTransparencyWaiver

/-- Deferral Waiver: one byte code -/
def DeferralWaiver.codes : List UInt8 :=
  [0x20, 0x36, 0x37, 0x38]

inductive DeferralWaiver where
  | immediatePublication -- Immediate Publication
  | nonImmediatePublicationDeferralForLargeInScaleLrgs -- Non Immediate Publication Deferral For Large In Scale Lrgs
  | nonImmediatePublicationDeferralForIlliquidInstrumentIlqd -- Non Immediate Publication Deferral For Illiquid Instrument Ilqd
  | nonImmediatePublicationDeferralForSizeSpecificSizeRts2 -- Non Immediate Publication Deferral For Size Specific Size Rts 2
  | unlisted (byte : { byte : UInt8 // byte ∉ DeferralWaiver.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeferralWaiver

def toByte : DeferralWaiver → UInt8
  | .immediatePublication => 0x20
  | .nonImmediatePublicationDeferralForLargeInScaleLrgs => 0x36
  | .nonImmediatePublicationDeferralForIlliquidInstrumentIlqd => 0x37
  | .nonImmediatePublicationDeferralForSizeSpecificSizeRts2 => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeferralWaiver :=
  if byte = 0x20 then .immediatePublication
  else if byte = 0x36 then .nonImmediatePublicationDeferralForLargeInScaleLrgs
  else if byte = 0x37 then .nonImmediatePublicationDeferralForIlliquidInstrumentIlqd
  else .nonImmediatePublicationDeferralForSizeSpecificSizeRts2

def ofByte (byte : UInt8) : DeferralWaiver :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeferralWaiver) : ofByte value.toByte = value := by
  cases value with
  | immediatePublication => decide
  | nonImmediatePublicationDeferralForLargeInScaleLrgs => decide
  | nonImmediatePublicationDeferralForIlliquidInstrumentIlqd => decide
  | nonImmediatePublicationDeferralForSizeSpecificSizeRts2 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeferralWaiver) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeferralWaiver × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeferralWaiver) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DeferralWaiver) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DeferralWaiver) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeferralWaiver

/-- Post Deferral Publication Type: one byte code -/
def PostDeferralPublicationType.codes : List UInt8 :=
  [0x20, 0x38]

inductive PostDeferralPublicationType where
  | notApplicableNoRelevantDeferralOrEnrichmentType -- Not Applicable No Relevant Deferral Or Enrichment Type
  | fullDetailsOfEarlierDailyAggregatedTradeDatf -- Full Details Of Earlier Daily Aggregated Trade Datf
  | unlisted (byte : { byte : UInt8 // byte ∉ PostDeferralPublicationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PostDeferralPublicationType

def toByte : PostDeferralPublicationType → UInt8
  | .notApplicableNoRelevantDeferralOrEnrichmentType => 0x20
  | .fullDetailsOfEarlierDailyAggregatedTradeDatf => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PostDeferralPublicationType :=
  if byte = 0x20 then .notApplicableNoRelevantDeferralOrEnrichmentType
  else .fullDetailsOfEarlierDailyAggregatedTradeDatf

def ofByte (byte : UInt8) : PostDeferralPublicationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PostDeferralPublicationType) : ofByte value.toByte = value := by
  cases value with
  | notApplicableNoRelevantDeferralOrEnrichmentType => decide
  | fullDetailsOfEarlierDailyAggregatedTradeDatf => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PostDeferralPublicationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PostDeferralPublicationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PostDeferralPublicationType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PostDeferralPublicationType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PostDeferralPublicationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PostDeferralPublicationType

/-- Amended Trade Type: one byte code -/
def AmendedTradeType.codes : List UInt8 :=
  [0x48, 0x4C, 0x4D, 0x52, 0x53, 0x57, 0x58, 0x33, 0x34, 0x36, 0x38, 0x39]

inductive AmendedTradeType where
  | crossTradeDuringTradingHours -- Cross Trade During Trading Hours
  | delta -- Delta
  | market -- Market
  | strategyTradesTimeSpreadFuturesAndStrategies -- Strategy Trades Time Spread Futures And Strategies
  | componentsOfTradeR -- Components Of Trade R
  | tradeAmendment -- Trade Amendment
  | countertrade -- Countertrade
  | rfq -- Rfq
  | rfqXRolling -- Rfq X Rolling
  | rfqXRollingDuringAuction -- Rfq X Rolling During Auction
  | rfqXRollingAmendment -- Rfq X Rolling Amendment
  | rfqXRollingDuringAuctionAmendment -- Rfq X Rolling During Auction Amendment
  | unlisted (byte : { byte : UInt8 // byte ∉ AmendedTradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AmendedTradeType

def toByte : AmendedTradeType → UInt8
  | .crossTradeDuringTradingHours => 0x48
  | .delta => 0x4C
  | .market => 0x4D
  | .strategyTradesTimeSpreadFuturesAndStrategies => 0x52
  | .componentsOfTradeR => 0x53
  | .tradeAmendment => 0x57
  | .countertrade => 0x58
  | .rfq => 0x33
  | .rfqXRolling => 0x34
  | .rfqXRollingDuringAuction => 0x36
  | .rfqXRollingAmendment => 0x38
  | .rfqXRollingDuringAuctionAmendment => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AmendedTradeType :=
  if byte = 0x48 then .crossTradeDuringTradingHours
  else if byte = 0x4C then .delta
  else if byte = 0x4D then .market
  else if byte = 0x52 then .strategyTradesTimeSpreadFuturesAndStrategies
  else if byte = 0x53 then .componentsOfTradeR
  else if byte = 0x57 then .tradeAmendment
  else if byte = 0x58 then .countertrade
  else if byte = 0x33 then .rfq
  else if byte = 0x34 then .rfqXRolling
  else if byte = 0x36 then .rfqXRollingDuringAuction
  else if byte = 0x38 then .rfqXRollingAmendment
  else .rfqXRollingDuringAuctionAmendment

def ofByte (byte : UInt8) : AmendedTradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AmendedTradeType) : ofByte value.toByte = value := by
  cases value with
  | crossTradeDuringTradingHours => decide
  | delta => decide
  | market => decide
  | strategyTradesTimeSpreadFuturesAndStrategies => decide
  | componentsOfTradeR => decide
  | tradeAmendment => decide
  | countertrade => decide
  | rfq => decide
  | rfqXRolling => decide
  | rfqXRollingDuringAuction => decide
  | rfqXRollingAmendment => decide
  | rfqXRollingDuringAuctionAmendment => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AmendedTradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AmendedTradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AmendedTradeType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AmendedTradeType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AmendedTradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AmendedTradeType

/-- Last Capacity 2: one byte code -/
def LastCapacity2.codes : List UInt8 :=
  [0x44, 0x4D, 0x41]

inductive LastCapacity2 where
  | dealingOnOwnAccount -- Dealing On Own Account
  | matchedPrincipal -- Matched Principal
  | anyOtherTradingCapacityBlanco -- Any Other Trading Capacity Blanco
  | unlisted (byte : { byte : UInt8 // byte ∉ LastCapacity2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LastCapacity2

def toByte : LastCapacity2 → UInt8
  | .dealingOnOwnAccount => 0x44
  | .matchedPrincipal => 0x4D
  | .anyOtherTradingCapacityBlanco => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LastCapacity2 :=
  if byte = 0x44 then .dealingOnOwnAccount
  else if byte = 0x4D then .matchedPrincipal
  else .anyOtherTradingCapacityBlanco

def ofByte (byte : UInt8) : LastCapacity2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LastCapacity2) : ofByte value.toByte = value := by
  cases value with
  | dealingOnOwnAccount => decide
  | matchedPrincipal => decide
  | anyOtherTradingCapacityBlanco => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LastCapacity2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LastCapacity2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LastCapacity2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LastCapacity2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LastCapacity2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LastCapacity2

/-- Persistence 2: one byte code -/
def Persistence2.codes : List UInt8 :=
  [0x43, 0x50]

inductive Persistence2 where
  | cancelOnDisconnection -- Cancel On Disconnection
  | persistOnDisconnection -- Persist On Disconnection
  | unlisted (byte : { byte : UInt8 // byte ∉ Persistence2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Persistence2

def toByte : Persistence2 → UInt8
  | .cancelOnDisconnection => 0x43
  | .persistOnDisconnection => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Persistence2 :=
  if byte = 0x43 then .cancelOnDisconnection
  else .persistOnDisconnection

def ofByte (byte : UInt8) : Persistence2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Persistence2) : ofByte value.toByte = value := by
  cases value with
  | cancelOnDisconnection => decide
  | persistOnDisconnection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Persistence2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Persistence2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Persistence2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Persistence2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Persistence2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Persistence2

/-- Self Match Prevention Type 2: one byte code -/
def SelfMatchPreventionType2.codes : List UInt8 :=
  [0x20, 0x31, 0x32, 0x33, 0x34]

inductive SelfMatchPreventionType2 where
  | naOrDefaultBehaviourAggressiveOrderIsRejected -- Na Or Default Behaviour Aggressive Order Is Rejected
  | rejectAggressiveOrder -- Reject Aggressive Order
  | cancel139AssiveOrder -- Cancel 139 Assive Order
  | cancelBothPassiveAndAggressiveOrder -- Cancel Both Passive And Aggressive Order
  | noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders -- No Order Gets Cancelled Both Aggressive And Passive Orders Remain Only Valid For Spain At Mid Direct Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ SelfMatchPreventionType2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SelfMatchPreventionType2

def toByte : SelfMatchPreventionType2 → UInt8
  | .naOrDefaultBehaviourAggressiveOrderIsRejected => 0x20
  | .rejectAggressiveOrder => 0x31
  | .cancel139AssiveOrder => 0x32
  | .cancelBothPassiveAndAggressiveOrder => 0x33
  | .noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SelfMatchPreventionType2 :=
  if byte = 0x20 then .naOrDefaultBehaviourAggressiveOrderIsRejected
  else if byte = 0x31 then .rejectAggressiveOrder
  else if byte = 0x32 then .cancel139AssiveOrder
  else if byte = 0x33 then .cancelBothPassiveAndAggressiveOrder
  else .noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders

def ofByte (byte : UInt8) : SelfMatchPreventionType2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SelfMatchPreventionType2) : ofByte value.toByte = value := by
  cases value with
  | naOrDefaultBehaviourAggressiveOrderIsRejected => decide
  | rejectAggressiveOrder => decide
  | cancel139AssiveOrder => decide
  | cancelBothPassiveAndAggressiveOrder => decide
  | noOrderGetsCancelledBothAggressiveAndPassiveOrdersRemainOnlyValidForSpainAtMidDirectOrders => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SelfMatchPreventionType2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SelfMatchPreventionType2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SelfMatchPreventionType2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SelfMatchPreventionType2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SelfMatchPreventionType2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SelfMatchPreventionType2

/-- Logon Response Message: 26 bytes -/
structure LogonResponseMessage where
  sequenceNumber : BitVec 32
  heartBtInt : BitVec 8
  protocolVersion : Alpha 6
  testProductionInd : Alpha 1
  environmentCode : Alpha 2
  sessionDate : BitVec 32
  expectedSequenceNumber : BitVec 32
  sequenceNumberTo : BitVec 32
  deriving DecidableEq, Repr

namespace LogonResponseMessage

def encode (message : LogonResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.heartBtInt
    ++ (Alpha.encode message.protocolVersion
    ++ (Alpha.encode message.testProductionInd
    ++ (Alpha.encode message.environmentCode
    ++ (encodeUIntLE 4 message.sessionDate
    ++ (encodeUIntLE 4 message.expectedSequenceNumber
    ++ (encodeUIntLE 4 message.sequenceNumberTo)))))))

def decode (bytes : List UInt8) : Option (LogonResponseMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (heartBtInt, bytes) ← decodeUIntLE 1 bytes
  let (protocolVersion, bytes) ← Alpha.decode 6 bytes
  let (testProductionInd, bytes) ← Alpha.decode 1 bytes
  let (environmentCode, bytes) ← Alpha.decode 2 bytes
  let (sessionDate, bytes) ← decodeUIntLE 4 bytes
  let (expectedSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sequenceNumberTo, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, heartBtInt, protocolVersion, testProductionInd, environmentCode, sessionDate, expectedSequenceNumber, sequenceNumberTo }, bytes)

@[simp] theorem encode_length (message : LogonResponseMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : LogonResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogonResponseMessage

/-- Logout Response Message: 5 bytes -/
structure LogoutResponseMessage where
  sequenceNumber : BitVec 32
  logoutReason : BitVec 8
  deriving DecidableEq, Repr

namespace LogoutResponseMessage

def encode (message : LogoutResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.logoutReason)

def decode (bytes : List UInt8) : Option (LogoutResponseMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (logoutReason, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, logoutReason }, bytes)

@[simp] theorem encode_length (message : LogoutResponseMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LogoutResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogoutResponseMessage

/-- Heartbeat Message: 4 bytes -/
structure HeartbeatMessage where
  sequenceNumber : BitVec 32
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (message : HeartbeatMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : HeartbeatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end HeartbeatMessage

/-- Network Status Message: 5 bytes -/
structure NetworkStatusMessage where
  sequenceNumber : BitVec 32
  networkStatusValue : BitVec 8
  deriving DecidableEq, Repr

namespace NetworkStatusMessage

def encode (message : NetworkStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.networkStatusValue)

def decode (bytes : List UInt8) : Option (NetworkStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (networkStatusValue, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, networkStatusValue }, bytes)

@[simp] theorem encode_length (message : NetworkStatusMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : NetworkStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetworkStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NetworkStatusMessage

/-- Logon Message: 53 bytes -/
structure LogonMessage where
  username : Alpha 7
  password : Alpha 10
  softwareName : Alpha 25
  expectedSequenceNumber : BitVec 32
  subscriptions : BitVec 8
  protocolVersion : Alpha 6
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.softwareName
    ++ (encodeUIntLE 4 message.expectedSequenceNumber
    ++ (encodeUIntLE 1 message.subscriptions
    ++ (Alpha.encode message.protocolVersion)))))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 7 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  let (softwareName, bytes) ← Alpha.decode 25 bytes
  let (expectedSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (subscriptions, bytes) ← decodeUIntLE 1 bytes
  let (protocolVersion, bytes) ← Alpha.decode 6 bytes
  pure ({ username, password, softwareName, expectedSequenceNumber, subscriptions, protocolVersion }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonMessage

/-- Reject Message: 70 bytes -/
structure RejectMessage where
  sequenceNumber : BitVec 32
  sessionRejectReason : BitVec 8
  textC58 : Alpha 58
  msgRejectedReference : Alpha 7
  deriving DecidableEq, Repr

namespace RejectMessage

def encode (message : RejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.sessionRejectReason
    ++ (Alpha.encode message.textC58
    ++ (Alpha.encode message.msgRejectedReference)))

def decode (bytes : List UInt8) : Option (RejectMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sessionRejectReason, bytes) ← decodeUIntLE 1 bytes
  let (textC58, bytes) ← Alpha.decode 58 bytes
  let (msgRejectedReference, bytes) ← Alpha.decode 7 bytes
  pure ({ sequenceNumber, sessionRejectReason, textC58, msgRejectedReference }, bytes)

@[simp] theorem encode_length (message : RejectMessage) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RejectMessage

/-- Trading Session Status Message: 15 bytes -/
structure TradingSessionStatusMessage where
  sequenceNumber : BitVec 32
  tradingSessionId : BitVec 8
  tradingSessionSubId : BitVec 8
  tradSesStatus : BitVec 8
  transactionDateAndTime : BitVec 64
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 1 message.tradingSessionSubId
    ++ (encodeUIntLE 1 message.tradSesStatus
    ++ (encodeUIntLE 8 message.transactionDateAndTime))))

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUIntLE 1 bytes
  let (tradSesStatus, bytes) ← decodeUIntLE 1 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, tradingSessionId, tradingSessionSubId, tradSesStatus, transactionDateAndTime }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradingSessionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradingSessionStatusMessage

/-- News Message: 82 bytes -/
structure NewsMessage where
  sequenceNumber : BitVec 32
  newsText : Alpha 78
  deriving DecidableEq, Repr

namespace NewsMessage

def encode (message : NewsMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.newsText)

def decode (bytes : List UInt8) : Option (NewsMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (newsText, bytes) ← Alpha.decode 78 bytes
  pure ({ sequenceNumber, newsText }, bytes)

@[simp] theorem encode_length (message : NewsMessage) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : NewsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewsMessage

/-- Security List Cancellation Report Message: 50 bytes -/
structure SecurityListCancellationReportMessage where
  sequenceNumber : BitVec 32
  marketId : Alpha 4
  marketSegmentId : Alpha 4
  securityCode : BitVec 32
  symbol : Alpha 22
  symbolIsin : Alpha 12
  deriving DecidableEq, Repr

namespace SecurityListCancellationReportMessage

def encode (message : SecurityListCancellationReportMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.marketId
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolIsin)))))

def decode (bytes : List UInt8) : Option (SecurityListCancellationReportMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 22 bytes
  let (symbolIsin, bytes) ← Alpha.decode 12 bytes
  pure ({ sequenceNumber, marketId, marketSegmentId, securityCode, symbol, symbolIsin }, bytes)

@[simp] theorem encode_length (message : SecurityListCancellationReportMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SecurityListCancellationReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityListCancellationReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityListCancellationReportMessage

/-- Statistics Message: 18 bytes -/
structure StatisticsMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  dataCount : BitVec 8
  dataCode : Alpha 1
  deriving DecidableEq, Repr

namespace StatisticsMessage

def encode (message : StatisticsMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 1 message.dataCount
    ++ (Alpha.encode message.dataCode))))

def decode (bytes : List UInt8) : Option (StatisticsMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (dataCount, bytes) ← decodeUIntLE 1 bytes
  let (dataCode, bytes) ← Alpha.decode 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, dataCount, dataCode }, bytes)

@[simp] theorem encode_length (message : StatisticsMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : StatisticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatisticsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StatisticsMessage

/-- Security List Message: 713 bytes -/
structure SecurityListMessage where
  sequenceNumber : BitVec 32
  marketId : Alpha 4
  marketSegmentId : Alpha 4
  securityCode : BitVec 32
  symbol : Alpha 22
  symbolIsin : Alpha 12
  fisn : Alpha 35
  issuerLei : Alpha 20
  securityGroup : Alpha 2
  familyCode : Alpha 5
  cfiCode : Alpha 6
  securityType : Alpha 2
  maturityDate : BitVec 32
  issueDate : BitVec 32
  contractMultiplier : BitVec 64
  liSpre : BitVec 64
  sstIpre : BitVec 64
  liSpost : BitVec 64
  sstIpost : BitVec 64
  liquidInstrument : BitVec 8
  admissionRequestedByIssuer : BitVec 8
  minTradeVol : BitVec 32
  roundLot : BitVec 32
  currency : Alpha 3
  modalityMaskB4 : BitVec 32
  securityDescription : Alpha 80
  tradingObligation : BitVec 8
  secDescription : Alpha 20
  underlyingAsset : Alpha 22
  securitySubType : Alpha 12
  maturityMonthYear : Alpha 8
  strikePrice : BitVec 64
  strikeValue : BitVec 64
  optAttribute : Alpha 1
  minPriceIncrement : BitVec 64
  unitOfMeasure : Alpha 20
  settlMethod : SettlMethod
  exerciseStyle : ExerciseStyle
  putOrCall : PutOrCall
  flexibleIndicator : FlexibleIndicator
  lastTradingDay : BitVec 32
  numberOfDecimals : BitVec 8
  orderNumberOfDecimals : BitVec 8
  adjustmentsRule : AdjustmentsRule
  maximumOrderSize : BitVec 64
  selfMatchPrevention : BitVec 8
  commodityDerivativeIndicator : CommodityDerivativeIndicator
  stockWhenUnderlyingIsDividend : Alpha 22
  baseProduct : Alpha 4
  subProduct : Alpha 4
  furtherSubProduct : Alpha 4
  baseCurrency : Alpha 3
  quotedCurrency : Alpha 3
  maturityMonthYearIncrementUnits : MaturityMonthYearIncrementUnits
  startMaturityMonthYear : Alpha 8
  endMaturityMonthYear : Alpha 8
  maturityMonthYearIncrement : BitVec 8
  underlyingSymbol : Alpha 22
  underlyingIsin : Alpha 12
  underlyingCurrency : Alpha 3
  underlyingSecurityIssuerLei : Alpha 20
  xRollingClosingType : XRollingClosingType
  xRollingReferenceBuyerRate : XRollingReferenceBuyerRate
  xRollingBuyerMarkup : BitVec 64
  xRollingReferenceSellerRate : XRollingReferenceSellerRate
  xRollingSellerMarkup : BitVec 64
  xRollingDividendPercentage : BitVec 64
  xRollingDividendPayDateDiff : BitVec 16
  legSymbol1 : Alpha 22
  legRatioQty1 : BitVec 32
  legSide1 : LegSide1
  legPrice1 : BitVec 64
  legSymbol2 : Alpha 22
  legRatioQty2 : BitVec 32
  legSide2 : LegSide2
  legPrice2 : BitVec 64
  legSymbol3 : Alpha 22
  legRatioQty3 : BitVec 32
  legSide3 : LegSide3
  legPrice3 : BitVec 64
  legSymbol4 : Alpha 22
  legRatioQty4 : BitVec 32
  legSide4 : LegSide4
  legPrice4 : BitVec 64
  legSymbol5 : Alpha 22
  legRatioQty5 : BitVec 32
  legSide5 : LegSide5
  legPrice5 : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityListMessage

def encode (message : SecurityListMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.marketId
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolIsin
    ++ (Alpha.encode message.fisn
    ++ (Alpha.encode message.issuerLei
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.familyCode
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.securityType
    ++ (encodeUIntLE 4 message.maturityDate
    ++ (encodeUIntLE 4 message.issueDate
    ++ (encodeUIntLE 8 message.contractMultiplier
    ++ (encodeUIntLE 8 message.liSpre
    ++ (encodeUIntLE 8 message.sstIpre
    ++ (encodeUIntLE 8 message.liSpost
    ++ (encodeUIntLE 8 message.sstIpost
    ++ (encodeUIntLE 1 message.liquidInstrument
    ++ (encodeUIntLE 1 message.admissionRequestedByIssuer
    ++ (encodeUIntLE 4 message.minTradeVol
    ++ (encodeUIntLE 4 message.roundLot
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 4 message.modalityMaskB4
    ++ (Alpha.encode message.securityDescription
    ++ (encodeUIntLE 1 message.tradingObligation
    ++ (Alpha.encode message.secDescription
    ++ (Alpha.encode message.underlyingAsset
    ++ (Alpha.encode message.securitySubType
    ++ (Alpha.encode message.maturityMonthYear
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 8 message.strikeValue
    ++ (Alpha.encode message.optAttribute
    ++ (encodeUIntLE 8 message.minPriceIncrement
    ++ (Alpha.encode message.unitOfMeasure
    ++ (SettlMethod.encode message.settlMethod
    ++ (ExerciseStyle.encode message.exerciseStyle
    ++ (PutOrCall.encode message.putOrCall
    ++ (FlexibleIndicator.encode message.flexibleIndicator
    ++ (encodeUIntLE 4 message.lastTradingDay
    ++ (encodeUIntLE 1 message.numberOfDecimals
    ++ (encodeUIntLE 1 message.orderNumberOfDecimals
    ++ (AdjustmentsRule.encode message.adjustmentsRule
    ++ (encodeUIntLE 8 message.maximumOrderSize
    ++ (encodeUIntLE 1 message.selfMatchPrevention
    ++ (CommodityDerivativeIndicator.encode message.commodityDerivativeIndicator
    ++ (Alpha.encode message.stockWhenUnderlyingIsDividend
    ++ (Alpha.encode message.baseProduct
    ++ (Alpha.encode message.subProduct
    ++ (Alpha.encode message.furtherSubProduct
    ++ (Alpha.encode message.baseCurrency
    ++ (Alpha.encode message.quotedCurrency
    ++ (MaturityMonthYearIncrementUnits.encode message.maturityMonthYearIncrementUnits
    ++ (Alpha.encode message.startMaturityMonthYear
    ++ (Alpha.encode message.endMaturityMonthYear
    ++ (encodeUIntLE 1 message.maturityMonthYearIncrement
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.underlyingIsin
    ++ (Alpha.encode message.underlyingCurrency
    ++ (Alpha.encode message.underlyingSecurityIssuerLei
    ++ (XRollingClosingType.encode message.xRollingClosingType
    ++ (XRollingReferenceBuyerRate.encode message.xRollingReferenceBuyerRate
    ++ (encodeUIntLE 8 message.xRollingBuyerMarkup
    ++ (XRollingReferenceSellerRate.encode message.xRollingReferenceSellerRate
    ++ (encodeUIntLE 8 message.xRollingSellerMarkup
    ++ (encodeUIntLE 8 message.xRollingDividendPercentage
    ++ (encodeUIntLE 2 message.xRollingDividendPayDateDiff
    ++ (Alpha.encode message.legSymbol1
    ++ (encodeUIntLE 4 message.legRatioQty1
    ++ (LegSide1.encode message.legSide1
    ++ (encodeUIntLE 8 message.legPrice1
    ++ (Alpha.encode message.legSymbol2
    ++ (encodeUIntLE 4 message.legRatioQty2
    ++ (LegSide2.encode message.legSide2
    ++ (encodeUIntLE 8 message.legPrice2
    ++ (Alpha.encode message.legSymbol3
    ++ (encodeUIntLE 4 message.legRatioQty3
    ++ (LegSide3.encode message.legSide3
    ++ (encodeUIntLE 8 message.legPrice3
    ++ (Alpha.encode message.legSymbol4
    ++ (encodeUIntLE 4 message.legRatioQty4
    ++ (LegSide4.encode message.legSide4
    ++ (encodeUIntLE 8 message.legPrice4
    ++ (Alpha.encode message.legSymbol5
    ++ (encodeUIntLE 4 message.legRatioQty5
    ++ (LegSide5.encode message.legSide5
    ++ (encodeUIntLE 8 message.legPrice5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecurityListMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 22 bytes
  let (symbolIsin, bytes) ← Alpha.decode 12 bytes
  let (fisn, bytes) ← Alpha.decode 35 bytes
  let (issuerLei, bytes) ← Alpha.decode 20 bytes
  let (securityGroup, bytes) ← Alpha.decode 2 bytes
  let (familyCode, bytes) ← Alpha.decode 5 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (securityType, bytes) ← Alpha.decode 2 bytes
  let (maturityDate, bytes) ← decodeUIntLE 4 bytes
  let (issueDate, bytes) ← decodeUIntLE 4 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (liSpre, bytes) ← decodeUIntLE 8 bytes
  let (sstIpre, bytes) ← decodeUIntLE 8 bytes
  let (liSpost, bytes) ← decodeUIntLE 8 bytes
  let (sstIpost, bytes) ← decodeUIntLE 8 bytes
  let (liquidInstrument, bytes) ← decodeUIntLE 1 bytes
  let (admissionRequestedByIssuer, bytes) ← decodeUIntLE 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (roundLot, bytes) ← decodeUIntLE 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (modalityMaskB4, bytes) ← decodeUIntLE 4 bytes
  let (securityDescription, bytes) ← Alpha.decode 80 bytes
  let (tradingObligation, bytes) ← decodeUIntLE 1 bytes
  let (secDescription, bytes) ← Alpha.decode 20 bytes
  let (underlyingAsset, bytes) ← Alpha.decode 22 bytes
  let (securitySubType, bytes) ← Alpha.decode 12 bytes
  let (maturityMonthYear, bytes) ← Alpha.decode 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (strikeValue, bytes) ← decodeUIntLE 8 bytes
  let (optAttribute, bytes) ← Alpha.decode 1 bytes
  let (minPriceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 20 bytes
  let (settlMethod, bytes) ← SettlMethod.decode bytes
  let (exerciseStyle, bytes) ← ExerciseStyle.decode bytes
  let (putOrCall, bytes) ← PutOrCall.decode bytes
  let (flexibleIndicator, bytes) ← FlexibleIndicator.decode bytes
  let (lastTradingDay, bytes) ← decodeUIntLE 4 bytes
  let (numberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (orderNumberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (adjustmentsRule, bytes) ← AdjustmentsRule.decode bytes
  let (maximumOrderSize, bytes) ← decodeUIntLE 8 bytes
  let (selfMatchPrevention, bytes) ← decodeUIntLE 1 bytes
  let (commodityDerivativeIndicator, bytes) ← CommodityDerivativeIndicator.decode bytes
  let (stockWhenUnderlyingIsDividend, bytes) ← Alpha.decode 22 bytes
  let (baseProduct, bytes) ← Alpha.decode 4 bytes
  let (subProduct, bytes) ← Alpha.decode 4 bytes
  let (furtherSubProduct, bytes) ← Alpha.decode 4 bytes
  let (baseCurrency, bytes) ← Alpha.decode 3 bytes
  let (quotedCurrency, bytes) ← Alpha.decode 3 bytes
  let (maturityMonthYearIncrementUnits, bytes) ← MaturityMonthYearIncrementUnits.decode bytes
  let (startMaturityMonthYear, bytes) ← Alpha.decode 8 bytes
  let (endMaturityMonthYear, bytes) ← Alpha.decode 8 bytes
  let (maturityMonthYearIncrement, bytes) ← decodeUIntLE 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 22 bytes
  let (underlyingIsin, bytes) ← Alpha.decode 12 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (underlyingSecurityIssuerLei, bytes) ← Alpha.decode 20 bytes
  let (xRollingClosingType, bytes) ← XRollingClosingType.decode bytes
  let (xRollingReferenceBuyerRate, bytes) ← XRollingReferenceBuyerRate.decode bytes
  let (xRollingBuyerMarkup, bytes) ← decodeUIntLE 8 bytes
  let (xRollingReferenceSellerRate, bytes) ← XRollingReferenceSellerRate.decode bytes
  let (xRollingSellerMarkup, bytes) ← decodeUIntLE 8 bytes
  let (xRollingDividendPercentage, bytes) ← decodeUIntLE 8 bytes
  let (xRollingDividendPayDateDiff, bytes) ← decodeUIntLE 2 bytes
  let (legSymbol1, bytes) ← Alpha.decode 22 bytes
  let (legRatioQty1, bytes) ← decodeUIntLE 4 bytes
  let (legSide1, bytes) ← LegSide1.decode bytes
  let (legPrice1, bytes) ← decodeUIntLE 8 bytes
  let (legSymbol2, bytes) ← Alpha.decode 22 bytes
  let (legRatioQty2, bytes) ← decodeUIntLE 4 bytes
  let (legSide2, bytes) ← LegSide2.decode bytes
  let (legPrice2, bytes) ← decodeUIntLE 8 bytes
  let (legSymbol3, bytes) ← Alpha.decode 22 bytes
  let (legRatioQty3, bytes) ← decodeUIntLE 4 bytes
  let (legSide3, bytes) ← LegSide3.decode bytes
  let (legPrice3, bytes) ← decodeUIntLE 8 bytes
  let (legSymbol4, bytes) ← Alpha.decode 22 bytes
  let (legRatioQty4, bytes) ← decodeUIntLE 4 bytes
  let (legSide4, bytes) ← LegSide4.decode bytes
  let (legPrice4, bytes) ← decodeUIntLE 8 bytes
  let (legSymbol5, bytes) ← Alpha.decode 22 bytes
  let (legRatioQty5, bytes) ← decodeUIntLE 4 bytes
  let (legSide5, bytes) ← LegSide5.decode bytes
  let (legPrice5, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, marketId, marketSegmentId, securityCode, symbol, symbolIsin, fisn, issuerLei, securityGroup, familyCode, cfiCode, securityType, maturityDate, issueDate, contractMultiplier, liSpre, sstIpre, liSpost, sstIpost, liquidInstrument, admissionRequestedByIssuer, minTradeVol, roundLot, currency, modalityMaskB4, securityDescription, tradingObligation, secDescription, underlyingAsset, securitySubType, maturityMonthYear, strikePrice, strikeValue, optAttribute, minPriceIncrement, unitOfMeasure, settlMethod, exerciseStyle, putOrCall, flexibleIndicator, lastTradingDay, numberOfDecimals, orderNumberOfDecimals, adjustmentsRule, maximumOrderSize, selfMatchPrevention, commodityDerivativeIndicator, stockWhenUnderlyingIsDividend, baseProduct, subProduct, furtherSubProduct, baseCurrency, quotedCurrency, maturityMonthYearIncrementUnits, startMaturityMonthYear, endMaturityMonthYear, maturityMonthYearIncrement, underlyingSymbol, underlyingIsin, underlyingCurrency, underlyingSecurityIssuerLei, xRollingClosingType, xRollingReferenceBuyerRate, xRollingBuyerMarkup, xRollingReferenceSellerRate, xRollingSellerMarkup, xRollingDividendPercentage, xRollingDividendPayDateDiff, legSymbol1, legRatioQty1, legSide1, legPrice1, legSymbol2, legRatioQty2, legSide2, legPrice2, legSymbol3, legRatioQty3, legSide3, legPrice3, legSymbol4, legRatioQty4, legSide4, legPrice4, legSymbol5, legRatioQty5, legSide5, legPrice5 }, bytes)

@[simp] theorem encode_length (message : SecurityListMessage) : (encode message).length = 713 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SettlMethod.encode_length, ExerciseStyle.encode_length, PutOrCall.encode_length, FlexibleIndicator.encode_length, AdjustmentsRule.encode_length, CommodityDerivativeIndicator.encode_length, MaturityMonthYearIncrementUnits.encode_length, XRollingClosingType.encode_length, XRollingReferenceBuyerRate.encode_length, XRollingReferenceSellerRate.encode_length, LegSide1.encode_length, LegSide2.encode_length, LegSide3.encode_length, LegSide4.encode_length, LegSide5.encode_length]

theorem encode_length_pos (message : SecurityListMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecurityListMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExerciseStyle.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PutOrCall.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FlexibleIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AdjustmentsRule.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CommodityDerivativeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaturityMonthYearIncrementUnits.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, XRollingClosingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, XRollingReferenceBuyerRate.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, XRollingReferenceSellerRate.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide4.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide5.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityListMessage

/-- Security List Update Report Message: 713 bytes -/
structure SecurityListUpdateReportMessage where
  sequenceNumber : BitVec 32
  marketId : Alpha 4
  marketSegmentId : Alpha 4
  securityCode : BitVec 32
  symbol : Alpha 22
  symbolIsin : Alpha 12
  fisn : Alpha 35
  issuerLei : Alpha 20
  securityGroup : Alpha 2
  familyCode : Alpha 5
  cfiCode : Alpha 6
  securityType : Alpha 2
  maturityDate : BitVec 32
  issueDate : BitVec 32
  contractMultiplier : BitVec 64
  liSpre : BitVec 64
  sstIpre : BitVec 64
  liSpost : BitVec 64
  sstIpost : BitVec 64
  liquidInstrument : BitVec 8
  admissionRequestedByIssuer : BitVec 8
  minTradeVol : BitVec 32
  roundLot : BitVec 32
  currency : Alpha 3
  modalityMaskB4 : BitVec 32
  securityDescription : Alpha 80
  tradingObligation : BitVec 8
  secDescription : Alpha 20
  underlyingAsset : Alpha 22
  securitySubType : Alpha 12
  maturityMonthYear : Alpha 8
  strikePrice : BitVec 64
  strikeValue : BitVec 64
  optAttribute : Alpha 1
  minPriceIncrement : BitVec 64
  unitOfMeasure : Alpha 20
  settlMethod : SettlMethod
  exerciseStyle : ExerciseStyle
  putOrCall : PutOrCall
  flexibleIndicator : FlexibleIndicator
  lastTradingDay : BitVec 32
  numberOfDecimals : BitVec 8
  orderNumberOfDecimals : BitVec 8
  adjustmentsRule : AdjustmentsRule
  maximumOrderSize : BitVec 64
  selfMatchPrevention : BitVec 8
  commodityDerivativeIndicator : CommodityDerivativeIndicator
  stockWhenUnderlyingIsDividend : Alpha 22
  baseProduct : Alpha 4
  subProduct : Alpha 4
  furtherSubProduct : Alpha 4
  baseCurrency : Alpha 3
  quotedCurrency : Alpha 3
  maturityMonthYearIncrementUnits : MaturityMonthYearIncrementUnits
  startMaturityMonthYear : Alpha 8
  endMaturityMonthYear : Alpha 8
  maturityMonthYearIncrement : BitVec 8
  underlyingSymbol : Alpha 22
  underlyingIsin : Alpha 12
  underlyingCurrency : Alpha 3
  underlyingSecurityIssuerLei : Alpha 20
  xRollingClosingType : XRollingClosingType
  xRollingReferenceBuyerRate : XRollingReferenceBuyerRate
  xRollingBuyerMarkup : BitVec 64
  xRollingReferenceSellerRate : XRollingReferenceSellerRate
  xRollingSellerMarkup : BitVec 64
  xRollingDividendPercentage : BitVec 64
  xRollingDividendPayDateDiff : BitVec 16
  legSymbol1 : Alpha 22
  legRatioQty1 : BitVec 32
  legSide1 : LegSide1
  legPrice1 : BitVec 64
  legSymbol2 : Alpha 22
  legRatioQty2 : BitVec 32
  legSide2 : LegSide2
  legPrice2 : BitVec 64
  legSymbol3 : Alpha 22
  legRatioQty3 : BitVec 32
  legSide3 : LegSide3
  legPrice3 : BitVec 64
  legSymbol4 : Alpha 22
  legRatioQty4 : BitVec 32
  legSide4 : LegSide4
  legPrice4 : BitVec 64
  legSymbol5 : Alpha 22
  legRatioQty5 : BitVec 32
  legSide5 : LegSide5
  legPrice5 : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityListUpdateReportMessage

def encode (message : SecurityListUpdateReportMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.marketId
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolIsin
    ++ (Alpha.encode message.fisn
    ++ (Alpha.encode message.issuerLei
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.familyCode
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.securityType
    ++ (encodeUIntLE 4 message.maturityDate
    ++ (encodeUIntLE 4 message.issueDate
    ++ (encodeUIntLE 8 message.contractMultiplier
    ++ (encodeUIntLE 8 message.liSpre
    ++ (encodeUIntLE 8 message.sstIpre
    ++ (encodeUIntLE 8 message.liSpost
    ++ (encodeUIntLE 8 message.sstIpost
    ++ (encodeUIntLE 1 message.liquidInstrument
    ++ (encodeUIntLE 1 message.admissionRequestedByIssuer
    ++ (encodeUIntLE 4 message.minTradeVol
    ++ (encodeUIntLE 4 message.roundLot
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 4 message.modalityMaskB4
    ++ (Alpha.encode message.securityDescription
    ++ (encodeUIntLE 1 message.tradingObligation
    ++ (Alpha.encode message.secDescription
    ++ (Alpha.encode message.underlyingAsset
    ++ (Alpha.encode message.securitySubType
    ++ (Alpha.encode message.maturityMonthYear
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 8 message.strikeValue
    ++ (Alpha.encode message.optAttribute
    ++ (encodeUIntLE 8 message.minPriceIncrement
    ++ (Alpha.encode message.unitOfMeasure
    ++ (SettlMethod.encode message.settlMethod
    ++ (ExerciseStyle.encode message.exerciseStyle
    ++ (PutOrCall.encode message.putOrCall
    ++ (FlexibleIndicator.encode message.flexibleIndicator
    ++ (encodeUIntLE 4 message.lastTradingDay
    ++ (encodeUIntLE 1 message.numberOfDecimals
    ++ (encodeUIntLE 1 message.orderNumberOfDecimals
    ++ (AdjustmentsRule.encode message.adjustmentsRule
    ++ (encodeUIntLE 8 message.maximumOrderSize
    ++ (encodeUIntLE 1 message.selfMatchPrevention
    ++ (CommodityDerivativeIndicator.encode message.commodityDerivativeIndicator
    ++ (Alpha.encode message.stockWhenUnderlyingIsDividend
    ++ (Alpha.encode message.baseProduct
    ++ (Alpha.encode message.subProduct
    ++ (Alpha.encode message.furtherSubProduct
    ++ (Alpha.encode message.baseCurrency
    ++ (Alpha.encode message.quotedCurrency
    ++ (MaturityMonthYearIncrementUnits.encode message.maturityMonthYearIncrementUnits
    ++ (Alpha.encode message.startMaturityMonthYear
    ++ (Alpha.encode message.endMaturityMonthYear
    ++ (encodeUIntLE 1 message.maturityMonthYearIncrement
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.underlyingIsin
    ++ (Alpha.encode message.underlyingCurrency
    ++ (Alpha.encode message.underlyingSecurityIssuerLei
    ++ (XRollingClosingType.encode message.xRollingClosingType
    ++ (XRollingReferenceBuyerRate.encode message.xRollingReferenceBuyerRate
    ++ (encodeUIntLE 8 message.xRollingBuyerMarkup
    ++ (XRollingReferenceSellerRate.encode message.xRollingReferenceSellerRate
    ++ (encodeUIntLE 8 message.xRollingSellerMarkup
    ++ (encodeUIntLE 8 message.xRollingDividendPercentage
    ++ (encodeUIntLE 2 message.xRollingDividendPayDateDiff
    ++ (Alpha.encode message.legSymbol1
    ++ (encodeUIntLE 4 message.legRatioQty1
    ++ (LegSide1.encode message.legSide1
    ++ (encodeUIntLE 8 message.legPrice1
    ++ (Alpha.encode message.legSymbol2
    ++ (encodeUIntLE 4 message.legRatioQty2
    ++ (LegSide2.encode message.legSide2
    ++ (encodeUIntLE 8 message.legPrice2
    ++ (Alpha.encode message.legSymbol3
    ++ (encodeUIntLE 4 message.legRatioQty3
    ++ (LegSide3.encode message.legSide3
    ++ (encodeUIntLE 8 message.legPrice3
    ++ (Alpha.encode message.legSymbol4
    ++ (encodeUIntLE 4 message.legRatioQty4
    ++ (LegSide4.encode message.legSide4
    ++ (encodeUIntLE 8 message.legPrice4
    ++ (Alpha.encode message.legSymbol5
    ++ (encodeUIntLE 4 message.legRatioQty5
    ++ (LegSide5.encode message.legSide5
    ++ (encodeUIntLE 8 message.legPrice5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecurityListUpdateReportMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 22 bytes
  let (symbolIsin, bytes) ← Alpha.decode 12 bytes
  let (fisn, bytes) ← Alpha.decode 35 bytes
  let (issuerLei, bytes) ← Alpha.decode 20 bytes
  let (securityGroup, bytes) ← Alpha.decode 2 bytes
  let (familyCode, bytes) ← Alpha.decode 5 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (securityType, bytes) ← Alpha.decode 2 bytes
  let (maturityDate, bytes) ← decodeUIntLE 4 bytes
  let (issueDate, bytes) ← decodeUIntLE 4 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (liSpre, bytes) ← decodeUIntLE 8 bytes
  let (sstIpre, bytes) ← decodeUIntLE 8 bytes
  let (liSpost, bytes) ← decodeUIntLE 8 bytes
  let (sstIpost, bytes) ← decodeUIntLE 8 bytes
  let (liquidInstrument, bytes) ← decodeUIntLE 1 bytes
  let (admissionRequestedByIssuer, bytes) ← decodeUIntLE 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (roundLot, bytes) ← decodeUIntLE 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (modalityMaskB4, bytes) ← decodeUIntLE 4 bytes
  let (securityDescription, bytes) ← Alpha.decode 80 bytes
  let (tradingObligation, bytes) ← decodeUIntLE 1 bytes
  let (secDescription, bytes) ← Alpha.decode 20 bytes
  let (underlyingAsset, bytes) ← Alpha.decode 22 bytes
  let (securitySubType, bytes) ← Alpha.decode 12 bytes
  let (maturityMonthYear, bytes) ← Alpha.decode 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (strikeValue, bytes) ← decodeUIntLE 8 bytes
  let (optAttribute, bytes) ← Alpha.decode 1 bytes
  let (minPriceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 20 bytes
  let (settlMethod, bytes) ← SettlMethod.decode bytes
  let (exerciseStyle, bytes) ← ExerciseStyle.decode bytes
  let (putOrCall, bytes) ← PutOrCall.decode bytes
  let (flexibleIndicator, bytes) ← FlexibleIndicator.decode bytes
  let (lastTradingDay, bytes) ← decodeUIntLE 4 bytes
  let (numberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (orderNumberOfDecimals, bytes) ← decodeUIntLE 1 bytes
  let (adjustmentsRule, bytes) ← AdjustmentsRule.decode bytes
  let (maximumOrderSize, bytes) ← decodeUIntLE 8 bytes
  let (selfMatchPrevention, bytes) ← decodeUIntLE 1 bytes
  let (commodityDerivativeIndicator, bytes) ← CommodityDerivativeIndicator.decode bytes
  let (stockWhenUnderlyingIsDividend, bytes) ← Alpha.decode 22 bytes
  let (baseProduct, bytes) ← Alpha.decode 4 bytes
  let (subProduct, bytes) ← Alpha.decode 4 bytes
  let (furtherSubProduct, bytes) ← Alpha.decode 4 bytes
  let (baseCurrency, bytes) ← Alpha.decode 3 bytes
  let (quotedCurrency, bytes) ← Alpha.decode 3 bytes
  let (maturityMonthYearIncrementUnits, bytes) ← MaturityMonthYearIncrementUnits.decode bytes
  let (startMaturityMonthYear, bytes) ← Alpha.decode 8 bytes
  let (endMaturityMonthYear, bytes) ← Alpha.decode 8 bytes
  let (maturityMonthYearIncrement, bytes) ← decodeUIntLE 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 22 bytes
  let (underlyingIsin, bytes) ← Alpha.decode 12 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (underlyingSecurityIssuerLei, bytes) ← Alpha.decode 20 bytes
  let (xRollingClosingType, bytes) ← XRollingClosingType.decode bytes
  let (xRollingReferenceBuyerRate, bytes) ← XRollingReferenceBuyerRate.decode bytes
  let (xRollingBuyerMarkup, bytes) ← decodeUIntLE 8 bytes
  let (xRollingReferenceSellerRate, bytes) ← XRollingReferenceSellerRate.decode bytes
  let (xRollingSellerMarkup, bytes) ← decodeUIntLE 8 bytes
  let (xRollingDividendPercentage, bytes) ← decodeUIntLE 8 bytes
  let (xRollingDividendPayDateDiff, bytes) ← decodeUIntLE 2 bytes
  let (legSymbol1, bytes) ← Alpha.decode 22 bytes
  let (legRatioQty1, bytes) ← decodeUIntLE 4 bytes
  let (legSide1, bytes) ← LegSide1.decode bytes
  let (legPrice1, bytes) ← decodeUIntLE 8 bytes
  let (legSymbol2, bytes) ← Alpha.decode 22 bytes
  let (legRatioQty2, bytes) ← decodeUIntLE 4 bytes
  let (legSide2, bytes) ← LegSide2.decode bytes
  let (legPrice2, bytes) ← decodeUIntLE 8 bytes
  let (legSymbol3, bytes) ← Alpha.decode 22 bytes
  let (legRatioQty3, bytes) ← decodeUIntLE 4 bytes
  let (legSide3, bytes) ← LegSide3.decode bytes
  let (legPrice3, bytes) ← decodeUIntLE 8 bytes
  let (legSymbol4, bytes) ← Alpha.decode 22 bytes
  let (legRatioQty4, bytes) ← decodeUIntLE 4 bytes
  let (legSide4, bytes) ← LegSide4.decode bytes
  let (legPrice4, bytes) ← decodeUIntLE 8 bytes
  let (legSymbol5, bytes) ← Alpha.decode 22 bytes
  let (legRatioQty5, bytes) ← decodeUIntLE 4 bytes
  let (legSide5, bytes) ← LegSide5.decode bytes
  let (legPrice5, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, marketId, marketSegmentId, securityCode, symbol, symbolIsin, fisn, issuerLei, securityGroup, familyCode, cfiCode, securityType, maturityDate, issueDate, contractMultiplier, liSpre, sstIpre, liSpost, sstIpost, liquidInstrument, admissionRequestedByIssuer, minTradeVol, roundLot, currency, modalityMaskB4, securityDescription, tradingObligation, secDescription, underlyingAsset, securitySubType, maturityMonthYear, strikePrice, strikeValue, optAttribute, minPriceIncrement, unitOfMeasure, settlMethod, exerciseStyle, putOrCall, flexibleIndicator, lastTradingDay, numberOfDecimals, orderNumberOfDecimals, adjustmentsRule, maximumOrderSize, selfMatchPrevention, commodityDerivativeIndicator, stockWhenUnderlyingIsDividend, baseProduct, subProduct, furtherSubProduct, baseCurrency, quotedCurrency, maturityMonthYearIncrementUnits, startMaturityMonthYear, endMaturityMonthYear, maturityMonthYearIncrement, underlyingSymbol, underlyingIsin, underlyingCurrency, underlyingSecurityIssuerLei, xRollingClosingType, xRollingReferenceBuyerRate, xRollingBuyerMarkup, xRollingReferenceSellerRate, xRollingSellerMarkup, xRollingDividendPercentage, xRollingDividendPayDateDiff, legSymbol1, legRatioQty1, legSide1, legPrice1, legSymbol2, legRatioQty2, legSide2, legPrice2, legSymbol3, legRatioQty3, legSide3, legPrice3, legSymbol4, legRatioQty4, legSide4, legPrice4, legSymbol5, legRatioQty5, legSide5, legPrice5 }, bytes)

@[simp] theorem encode_length (message : SecurityListUpdateReportMessage) : (encode message).length = 713 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SettlMethod.encode_length, ExerciseStyle.encode_length, PutOrCall.encode_length, FlexibleIndicator.encode_length, AdjustmentsRule.encode_length, CommodityDerivativeIndicator.encode_length, MaturityMonthYearIncrementUnits.encode_length, XRollingClosingType.encode_length, XRollingReferenceBuyerRate.encode_length, XRollingReferenceSellerRate.encode_length, LegSide1.encode_length, LegSide2.encode_length, LegSide3.encode_length, LegSide4.encode_length, LegSide5.encode_length]

theorem encode_length_pos (message : SecurityListUpdateReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecurityListUpdateReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExerciseStyle.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PutOrCall.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FlexibleIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AdjustmentsRule.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CommodityDerivativeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaturityMonthYearIncrementUnits.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, XRollingClosingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, XRollingReferenceBuyerRate.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, XRollingReferenceSellerRate.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide4.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide5.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityListUpdateReportMessage

/-- Security Status Message: 34 bytes -/
structure SecurityStatusMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  securityTradingStatus : BitVec 8
  nonAvailabilityReason : BitVec 8
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 1 message.securityTradingStatus
    ++ (encodeUIntLE 1 message.nonAvailabilityReason
    ++ (encodeUIntLE 8 message.highLimitPrice
    ++ (encodeUIntLE 8 message.lowLimitPrice))))))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (securityTradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (nonAvailabilityReason, bytes) ← decodeUIntLE 1 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, securityTradingStatus, nonAvailabilityReason, highLimitPrice, lowLimitPrice }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityStatusMessage

/-- Family Status Message: 21 bytes -/
structure FamilyStatusMessage where
  sequenceNumber : BitVec 32
  securityGroup : Alpha 2
  familyCode : Alpha 5
  transactionDateAndTime : BitVec 64
  securityTradingStatus : BitVec 8
  nonAvailabilityReason : BitVec 8
  deriving DecidableEq, Repr

namespace FamilyStatusMessage

def encode (message : FamilyStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.familyCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 1 message.securityTradingStatus
    ++ (encodeUIntLE 1 message.nonAvailabilityReason)))))

def decode (bytes : List UInt8) : Option (FamilyStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityGroup, bytes) ← Alpha.decode 2 bytes
  let (familyCode, bytes) ← Alpha.decode 5 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (securityTradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (nonAvailabilityReason, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityGroup, familyCode, transactionDateAndTime, securityTradingStatus, nonAvailabilityReason }, bytes)

@[simp] theorem encode_length (message : FamilyStatusMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : FamilyStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FamilyStatusMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end FamilyStatusMessage

/-- Order Cancellation Market Member Message: 24 bytes -/
structure OrderCancellationMarketMemberMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancellationMarketMemberMessage

def encode (message : OrderCancellationMarketMemberMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate))))

def decode (bytes : List UInt8) : Option (OrderCancellationMarketMemberMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, entryDate }, bytes)

@[simp] theorem encode_length (message : OrderCancellationMarketMemberMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancellationMarketMemberMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationMarketMemberMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancellationMarketMemberMessage

/-- Quote Cancellation Market Member Message: 24 bytes -/
structure QuoteCancellationMarketMemberMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  secondaryOrderId2 : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteCancellationMarketMemberMessage

def encode (message : QuoteCancellationMarketMemberMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.secondaryOrderId2))))

def decode (bytes : List UInt8) : Option (QuoteCancellationMarketMemberMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, secondaryOrderId2 }, bytes)

@[simp] theorem encode_length (message : QuoteCancellationMarketMemberMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteCancellationMarketMemberMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteCancellationMarketMemberMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteCancellationMarketMemberMessage

/-- Indication Of Interest Message: 36 bytes -/
structure IndicationOfInterestMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  ioiid : BitVec 32
  ioiTransType : IoiTransType
  side : Side
  ioiQty : BitVec 32
  ioiPrice : BitVec 64
  ioiQltyInd : IoiQltyInd
  tradingSessionId : BitVec 8
  deriving DecidableEq, Repr

namespace IndicationOfInterestMessage

def encode (message : IndicationOfInterestMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.ioiid
    ++ (IoiTransType.encode message.ioiTransType
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.ioiQty
    ++ (encodeUIntLE 8 message.ioiPrice
    ++ (IoiQltyInd.encode message.ioiQltyInd
    ++ (encodeUIntLE 1 message.tradingSessionId)))))))))

def decode (bytes : List UInt8) : Option (IndicationOfInterestMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (ioiid, bytes) ← decodeUIntLE 4 bytes
  let (ioiTransType, bytes) ← IoiTransType.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (ioiQty, bytes) ← decodeUIntLE 4 bytes
  let (ioiPrice, bytes) ← decodeUIntLE 8 bytes
  let (ioiQltyInd, bytes) ← IoiQltyInd.decode bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, ioiid, ioiTransType, side, ioiQty, ioiPrice, ioiQltyInd, tradingSessionId }, bytes)

@[simp] theorem encode_length (message : IndicationOfInterestMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, IoiTransType.encode_length, Side.encode_length, IoiQltyInd.encode_length]

theorem encode_length_pos (message : IndicationOfInterestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicationOfInterestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, IoiTransType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, IoiQltyInd.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndicationOfInterestMessage

/-- Order And Quote Client Data Message: 78 bytes -/
structure OrderAndQuoteClientDataMessage where
  requestId : BitVec 32
  clientDataId : BitVec 16
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  persistence : Persistence
  selfMatchPreventionType : SelfMatchPreventionType
  clientDataReference : Alpha 15
  deriving DecidableEq, Repr

namespace OrderAndQuoteClientDataMessage

def encode (message : OrderAndQuoteClientDataMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (Persistence.encode message.persistence
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.clientDataReference))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAndQuoteClientDataMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (clientDataReference, bytes) ← Alpha.decode 15 bytes
  pure ({ requestId, clientDataId, algorithmicTradeIndicator, clientId, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, persistence, selfMatchPreventionType, clientDataReference }, bytes)

@[simp] theorem encode_length (message : OrderAndQuoteClientDataMessage) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LastCapacity.encode_length, Persistence.encode_length, SelfMatchPreventionType.encode_length]

theorem encode_length_pos (message : OrderAndQuoteClientDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAndQuoteClientDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderAndQuoteClientDataMessage

/-- Delta Protection Parameters Message: 12 bytes -/
structure DeltaProtectionParametersMessage where
  requestId : BitVec 32
  securityGroup : Alpha 2
  productType : Alpha 1
  deltaProtectionTime : BitVec 8
  deltaProtectionVolume : BitVec 32
  deriving DecidableEq, Repr

namespace DeltaProtectionParametersMessage

def encode (message : DeltaProtectionParametersMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.productType
    ++ (encodeUIntLE 1 message.deltaProtectionTime
    ++ (encodeUIntLE 4 message.deltaProtectionVolume))))

def decode (bytes : List UInt8) : Option (DeltaProtectionParametersMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityGroup, bytes) ← Alpha.decode 2 bytes
  let (productType, bytes) ← Alpha.decode 1 bytes
  let (deltaProtectionTime, bytes) ← decodeUIntLE 1 bytes
  let (deltaProtectionVolume, bytes) ← decodeUIntLE 4 bytes
  pure ({ requestId, securityGroup, productType, deltaProtectionTime, deltaProtectionVolume }, bytes)

@[simp] theorem encode_length (message : DeltaProtectionParametersMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : DeltaProtectionParametersMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeltaProtectionParametersMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DeltaProtectionParametersMessage

/-- Simple New Order Message: 28 bytes -/
structure SimpleNewOrderMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  clientDataId : BitVec 16
  orderId : BitVec 32
  side : Side
  price : BitVec 64
  orderQty : BitVec 32
  timeInForce : Alpha 1
  deriving DecidableEq, Repr

namespace SimpleNewOrderMessage

def encode (message : SimpleNewOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (Alpha.encode message.timeInForce)))))))

def decode (bytes : List UInt8) : Option (SimpleNewOrderMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (timeInForce, bytes) ← Alpha.decode 1 bytes
  pure ({ requestId, securityCode, clientDataId, orderId, side, price, orderQty, timeInForce }, bytes)

@[simp] theorem encode_length (message : SimpleNewOrderMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : SimpleNewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleNewOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleNewOrderMessage

/-- Simple New Order With Client Data Message: 98 bytes -/
structure SimpleNewOrderWithClientDataMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  orderId : BitVec 32
  side : Side
  price : BitVec 64
  orderQty : BitVec 32
  timeInForce : Alpha 1
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  persistence : Persistence
  selfMatchPreventionType : SelfMatchPreventionType
  clientDataReference : Alpha 15
  deriving DecidableEq, Repr

namespace SimpleNewOrderWithClientDataMessage

def encode (message : SimpleNewOrderWithClientDataMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (Alpha.encode message.timeInForce
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (Persistence.encode message.persistence
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.clientDataReference)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SimpleNewOrderWithClientDataMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (timeInForce, bytes) ← Alpha.decode 1 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (clientDataReference, bytes) ← Alpha.decode 15 bytes
  pure ({ requestId, securityCode, orderId, side, price, orderQty, timeInForce, algorithmicTradeIndicator, clientId, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, persistence, selfMatchPreventionType, clientDataReference }, bytes)

@[simp] theorem encode_length (message : SimpleNewOrderWithClientDataMessage) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length, LastCapacity.encode_length, Persistence.encode_length, SelfMatchPreventionType.encode_length]

theorem encode_length_pos (message : SimpleNewOrderWithClientDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleNewOrderWithClientDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleNewOrderWithClientDataMessage

/-- Simple Order Modification Message: 27 bytes -/
structure SimpleOrderModificationMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  orderId : BitVec 32
  side : Side
  price : BitVec 64
  orderQty : BitVec 32
  clientDataId : BitVec 16
  deriving DecidableEq, Repr

namespace SimpleOrderModificationMessage

def encode (message : SimpleOrderModificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 2 message.clientDataId))))))

def decode (bytes : List UInt8) : Option (SimpleOrderModificationMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  pure ({ requestId, securityCode, orderId, side, price, orderQty, clientDataId }, bytes)

@[simp] theorem encode_length (message : SimpleOrderModificationMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length]

theorem encode_length_pos (message : SimpleOrderModificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleOrderModificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SimpleOrderModificationMessage

/-- Simple Order Modification With Client Data Message: 97 bytes -/
structure SimpleOrderModificationWithClientDataMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  orderId : BitVec 32
  side : Side
  price : BitVec 64
  orderQty : BitVec 32
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  persistence : Persistence
  selfMatchPreventionType : SelfMatchPreventionType
  clientDataReference : Alpha 15
  deriving DecidableEq, Repr

namespace SimpleOrderModificationWithClientDataMessage

def encode (message : SimpleOrderModificationWithClientDataMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (Persistence.encode message.persistence
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.clientDataReference))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SimpleOrderModificationWithClientDataMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (clientDataReference, bytes) ← Alpha.decode 15 bytes
  pure ({ requestId, securityCode, orderId, side, price, orderQty, algorithmicTradeIndicator, clientId, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, persistence, selfMatchPreventionType, clientDataReference }, bytes)

@[simp] theorem encode_length (message : SimpleOrderModificationWithClientDataMessage) : (encode message).length = 97 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length, LastCapacity.encode_length, Persistence.encode_length, SelfMatchPreventionType.encode_length]

theorem encode_length_pos (message : SimpleOrderModificationWithClientDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleOrderModificationWithClientDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleOrderModificationWithClientDataMessage

/-- Order Cancellation Request Message: 12 bytes -/
structure OrderCancellationRequestMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  orderId : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancellationRequestMessage

def encode (message : OrderCancellationRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.orderId))

def decode (bytes : List UInt8) : Option (OrderCancellationRequestMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  pure ({ requestId, securityCode, orderId }, bytes)

@[simp] theorem encode_length (message : OrderCancellationRequestMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancellationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancellationRequestMessage

/-- New Quote Message: 34 bytes -/
structure NewQuoteMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  clientDataId : BitVec 16
  bidSize1 : BitVec 32
  bidPx1 : BitVec 64
  askSize1 : BitVec 32
  askPx1 : BitVec 64
  deriving DecidableEq, Repr

namespace NewQuoteMessage

def encode (message : NewQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 4 message.bidSize1
    ++ (encodeUIntLE 8 message.bidPx1
    ++ (encodeUIntLE 4 message.askSize1
    ++ (encodeUIntLE 8 message.askPx1))))))

def decode (bytes : List UInt8) : Option (NewQuoteMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (bidSize1, bytes) ← decodeUIntLE 4 bytes
  let (bidPx1, bytes) ← decodeUIntLE 8 bytes
  let (askSize1, bytes) ← decodeUIntLE 4 bytes
  let (askPx1, bytes) ← decodeUIntLE 8 bytes
  pure ({ requestId, securityCode, clientDataId, bidSize1, bidPx1, askSize1, askPx1 }, bytes)

@[simp] theorem encode_length (message : NewQuoteMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : NewQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NewQuoteMessage

/-- Quote Modification Request Message: 26 bytes -/
structure QuoteModificationRequestMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  clientDataId : BitVec 16
  bidPx1 : BitVec 64
  askPx1 : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteModificationRequestMessage

def encode (message : QuoteModificationRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 8 message.bidPx1
    ++ (encodeUIntLE 8 message.askPx1))))

def decode (bytes : List UInt8) : Option (QuoteModificationRequestMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (bidPx1, bytes) ← decodeUIntLE 8 bytes
  let (askPx1, bytes) ← decodeUIntLE 8 bytes
  pure ({ requestId, securityCode, clientDataId, bidPx1, askPx1 }, bytes)

@[simp] theorem encode_length (message : QuoteModificationRequestMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteModificationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteModificationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteModificationRequestMessage

/-- Quote Cancellation Request Message: 10 bytes -/
structure QuoteCancellationRequestMessage where
  requestId : BitVec 32
  securityCode : BitVec 32
  clientDataId : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteCancellationRequestMessage

def encode (message : QuoteCancellationRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 2 message.clientDataId))

def decode (bytes : List UInt8) : Option (QuoteCancellationRequestMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  pure ({ requestId, securityCode, clientDataId }, bytes)

@[simp] theorem encode_length (message : QuoteCancellationRequestMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteCancellationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteCancellationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteCancellationRequestMessage

/-- Mass Orderquote Cancellation Message: 18 bytes -/
structure MassOrderquoteCancellationMessage where
  requestId : BitVec 32
  account : Alpha 5
  securityGroup : Alpha 2
  securityCode : BitVec 32
  productType : Alpha 1
  side : Side
  orderOrQuoteCancel : OrderOrQuoteCancel
  deriving DecidableEq, Repr

namespace MassOrderquoteCancellationMessage

def encode (message : MassOrderquoteCancellationMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.securityGroup
    ++ (encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.productType
    ++ (Side.encode message.side
    ++ (OrderOrQuoteCancel.encode message.orderOrQuoteCancel))))))

def decode (bytes : List UInt8) : Option (MassOrderquoteCancellationMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (securityGroup, bytes) ← Alpha.decode 2 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (productType, bytes) ← Alpha.decode 1 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderOrQuoteCancel, bytes) ← OrderOrQuoteCancel.decode bytes
  pure ({ requestId, account, securityGroup, securityCode, productType, side, orderOrQuoteCancel }, bytes)

@[simp] theorem encode_length (message : MassOrderquoteCancellationMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Side.encode_length, OrderOrQuoteCancel.encode_length]

theorem encode_length_pos (message : MassOrderquoteCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassOrderquoteCancellationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [OrderOrQuoteCancel.decode_encode, some_bind]
  rfl

end MassOrderquoteCancellationMessage

/-- Order And Quote Client Data Parameters Ack Nack Message: 83 bytes -/
structure OrderAndQuoteClientDataParametersAckNackMessage where
  sequenceNumber : BitVec 32
  requestId : BitVec 32
  status : BitVec 8
  clientDataId : BitVec 16
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  persistence : Persistence
  selfMatchPreventionType : SelfMatchPreventionType
  clientDataReference : Alpha 15
  deriving DecidableEq, Repr

namespace OrderAndQuoteClientDataParametersAckNackMessage

def encode (message : OrderAndQuoteClientDataParametersAckNackMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 1 message.status
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (Persistence.encode message.persistence
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.clientDataReference))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAndQuoteClientDataParametersAckNackMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (status, bytes) ← decodeUIntLE 1 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (clientDataReference, bytes) ← Alpha.decode 15 bytes
  pure ({ sequenceNumber, requestId, status, clientDataId, algorithmicTradeIndicator, clientId, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, persistence, selfMatchPreventionType, clientDataReference }, bytes)

@[simp] theorem encode_length (message : OrderAndQuoteClientDataParametersAckNackMessage) : (encode message).length = 83 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LastCapacity.encode_length, Persistence.encode_length, SelfMatchPreventionType.encode_length]

theorem encode_length_pos (message : OrderAndQuoteClientDataParametersAckNackMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAndQuoteClientDataParametersAckNackMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderAndQuoteClientDataParametersAckNackMessage

/-- Delta Protection Parameters Ack Nack Message: 17 bytes -/
structure DeltaProtectionParametersAckNackMessage where
  sequenceNumber : BitVec 32
  requestId : BitVec 32
  status : BitVec 8
  securityGroup : Alpha 2
  productType : Alpha 1
  deltaProtectionTime : BitVec 8
  deltaProtectionVolume : BitVec 32
  deriving DecidableEq, Repr

namespace DeltaProtectionParametersAckNackMessage

def encode (message : DeltaProtectionParametersAckNackMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 1 message.status
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.productType
    ++ (encodeUIntLE 1 message.deltaProtectionTime
    ++ (encodeUIntLE 4 message.deltaProtectionVolume))))))

def decode (bytes : List UInt8) : Option (DeltaProtectionParametersAckNackMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (status, bytes) ← decodeUIntLE 1 bytes
  let (securityGroup, bytes) ← Alpha.decode 2 bytes
  let (productType, bytes) ← Alpha.decode 1 bytes
  let (deltaProtectionTime, bytes) ← decodeUIntLE 1 bytes
  let (deltaProtectionVolume, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, requestId, status, securityGroup, productType, deltaProtectionTime, deltaProtectionVolume }, bytes)

@[simp] theorem encode_length (message : DeltaProtectionParametersAckNackMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : DeltaProtectionParametersAckNackMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeltaProtectionParametersAckNackMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DeltaProtectionParametersAckNackMessage

/-- Simple Order Status Message: 62 bytes -/
structure SimpleOrderStatusMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  side : Side
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ordRejReason : OrdRejReason
  execType : ExecType
  requestId : BitVec 32
  clientDataId : BitVec 16
  deriving DecidableEq, Repr

namespace SimpleOrderStatusMessage

def encode (message : SimpleOrderStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (OrdRejReason.encode message.ordRejReason
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId))))))))))))))))

def decode (bytes : List UInt8) : Option (SimpleOrderStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ordRejReason, bytes) ← OrdRejReason.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, entryDate, side, priority, price, displayQty, orderId, secondaryExecId, orderQty, ordStatus, ordRejReason, execType, requestId, clientDataId }, bytes)

@[simp] theorem encode_length (message : SimpleOrderStatusMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, OrdStatus.encode_length, OrdRejReason.encode_length, ExecType.encode_length]

theorem encode_length_pos (message : SimpleOrderStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleOrderStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdRejReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SimpleOrderStatusMessage

/-- Quote Status Message: 92 bytes -/
structure QuoteStatusMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  secondaryOrderId2 : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  priority2 : BitVec 32
  price2 : BitVec 64
  displayQty2 : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ordRejReason : OrdRejReason
  execType : ExecType
  orderId2 : BitVec 32
  secondaryExecId2 : BitVec 32
  orderQty2 : BitVec 32
  ordStatus2 : OrdStatus2
  ordRejReason2 : OrdRejReason2
  execType2 : ExecType2
  requestId : BitVec 32
  clientDataId : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteStatusMessage

def encode (message : QuoteStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.priority2
    ++ (encodeUIntLE 8 message.price2
    ++ (encodeUIntLE 4 message.displayQty2
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (OrdRejReason.encode message.ordRejReason
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 4 message.orderId2
    ++ (encodeUIntLE 4 message.secondaryExecId2
    ++ (encodeUIntLE 4 message.orderQty2
    ++ (OrdStatus2.encode message.ordStatus2
    ++ (OrdRejReason2.encode message.ordRejReason2
    ++ (ExecType2.encode message.execType2
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (QuoteStatusMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (priority2, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 8 bytes
  let (displayQty2, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ordRejReason, bytes) ← OrdRejReason.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (orderId2, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId2, bytes) ← decodeUIntLE 4 bytes
  let (orderQty2, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus2, bytes) ← OrdStatus2.decode bytes
  let (ordRejReason2, bytes) ← OrdRejReason2.decode bytes
  let (execType2, bytes) ← ExecType2.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, secondaryOrderId2, priority, price, displayQty, priority2, price2, displayQty2, orderId, secondaryExecId, orderQty, ordStatus, ordRejReason, execType, orderId2, secondaryExecId2, orderQty2, ordStatus2, ordRejReason2, execType2, requestId, clientDataId }, bytes)

@[simp] theorem encode_length (message : QuoteStatusMessage) : (encode message).length = 92 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrdStatus.encode_length, OrdRejReason.encode_length, ExecType.encode_length, OrdStatus2.encode_length, OrdRejReason2.encode_length, ExecType2.encode_length]

theorem encode_length_pos (message : QuoteStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : QuoteStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdRejReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdRejReason2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteStatusMessage

/-- Order Cancel Reject Message: 19 bytes -/
structure OrderCancelRejectMessage where
  sequenceNumber : BitVec 32
  transactionDateAndTime : BitVec 64
  orderId : BitVec 32
  ordStatus : OrdStatus
  cxlRejResponseTo : CxlRejResponseTo
  cxlRejReason : CxlRejReason
  deriving DecidableEq, Repr

namespace OrderCancelRejectMessage

def encode (message : OrderCancelRejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.orderId
    ++ (OrdStatus.encode message.ordStatus
    ++ (CxlRejResponseTo.encode message.cxlRejResponseTo
    ++ (CxlRejReason.encode message.cxlRejReason)))))

def decode (bytes : List UInt8) : Option (OrderCancelRejectMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (cxlRejResponseTo, bytes) ← CxlRejResponseTo.decode bytes
  let (cxlRejReason, bytes) ← CxlRejReason.decode bytes
  pure ({ sequenceNumber, transactionDateAndTime, orderId, ordStatus, cxlRejResponseTo, cxlRejReason }, bytes)

@[simp] theorem encode_length (message : OrderCancelRejectMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrdStatus.encode_length, CxlRejResponseTo.encode_length, CxlRejReason.encode_length]

theorem encode_length_pos (message : OrderCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CxlRejResponseTo.decode_encode, some_bind]
  dsimp only
  rw [CxlRejReason.decode_encode, some_bind]
  rfl

end OrderCancelRejectMessage

/-- Mass Orderquote Cancellation Completion Message: 18 bytes -/
structure MassOrderquoteCancellationCompletionMessage where
  sequenceNumber : BitVec 32
  transactionDateAndTime : BitVec 64
  tradingUnit : BitVec 8
  orderOrQuoteCancel : OrderOrQuoteCancel
  requestId : BitVec 32
  deriving DecidableEq, Repr

namespace MassOrderquoteCancellationCompletionMessage

def encode (message : MassOrderquoteCancellationCompletionMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 1 message.tradingUnit
    ++ (OrderOrQuoteCancel.encode message.orderOrQuoteCancel
    ++ (encodeUIntLE 4 message.requestId))))

def decode (bytes : List UInt8) : Option (MassOrderquoteCancellationCompletionMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingUnit, bytes) ← decodeUIntLE 1 bytes
  let (orderOrQuoteCancel, bytes) ← OrderOrQuoteCancel.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, transactionDateAndTime, tradingUnit, orderOrQuoteCancel, requestId }, bytes)

@[simp] theorem encode_length (message : MassOrderquoteCancellationCompletionMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderOrQuoteCancel.encode_length]

theorem encode_length_pos (message : MassOrderquoteCancellationCompletionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassOrderquoteCancellationCompletionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderOrQuoteCancel.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MassOrderquoteCancellationCompletionMessage

/-- Mass Orderquote Cancellation Reject Message: 14 bytes -/
structure MassOrderquoteCancellationRejectMessage where
  sequenceNumber : BitVec 32
  transactionDateAndTime : BitVec 64
  tradingUnit : BitVec 8
  massCancelRejectReason : MassCancelRejectReason
  deriving DecidableEq, Repr

namespace MassOrderquoteCancellationRejectMessage

def encode (message : MassOrderquoteCancellationRejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 1 message.tradingUnit
    ++ (MassCancelRejectReason.encode message.massCancelRejectReason)))

def decode (bytes : List UInt8) : Option (MassOrderquoteCancellationRejectMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingUnit, bytes) ← decodeUIntLE 1 bytes
  let (massCancelRejectReason, bytes) ← MassCancelRejectReason.decode bytes
  pure ({ sequenceNumber, transactionDateAndTime, tradingUnit, massCancelRejectReason }, bytes)

@[simp] theorem encode_length (message : MassOrderquoteCancellationRejectMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MassCancelRejectReason.encode_length]

theorem encode_length_pos (message : MassOrderquoteCancellationRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassOrderquoteCancellationRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [MassCancelRejectReason.decode_encode, some_bind]
  rfl

end MassOrderquoteCancellationRejectMessage

/-- Business Message Reject Message: 79 bytes -/
structure BusinessMessageRejectMessage where
  sequenceNumber : BitVec 32
  transactionDateAndTime : BitVec 64
  refMsgType : BitVec 8
  businessRejectReason : BitVec 8
  textC65 : Alpha 65
  deriving DecidableEq, Repr

namespace BusinessMessageRejectMessage

def encode (message : BusinessMessageRejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 1 message.refMsgType
    ++ (encodeUIntLE 1 message.businessRejectReason
    ++ (Alpha.encode message.textC65))))

def decode (bytes : List UInt8) : Option (BusinessMessageRejectMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (refMsgType, bytes) ← decodeUIntLE 1 bytes
  let (businessRejectReason, bytes) ← decodeUIntLE 1 bytes
  let (textC65, bytes) ← Alpha.decode 65 bytes
  pure ({ sequenceNumber, transactionDateAndTime, refMsgType, businessRejectReason, textC65 }, bytes)

@[simp] theorem encode_length (message : BusinessMessageRejectMessage) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : BusinessMessageRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BusinessMessageRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BusinessMessageRejectMessage

/-- Execution Private Information 2 Legs Message: 144 bytes -/
structure ExecutionPrivateInformation2LegsMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  transactionCategory : TransactionCategory
  strategyTrdMatchId : BitVec 32
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ccpCode : CcpCode
  aggressorIndicator : AggressorIndicator
  requestId : BitVec 32
  clientDataId : BitVec 16
  secondaryOrderId2 : BitVec 32
  entryDate2 : BitVec 32
  priority2 : BitVec 32
  price2 : BitVec 64
  displayQty2 : BitVec 32
  orderId2 : BitVec 32
  secondaryExecId2 : BitVec 32
  orderQty2 : BitVec 32
  ordStatus2 : OrdStatus2
  ccpCode2 : CcpCode2
  aggressorIndicator2 : AggressorIndicator2
  requestId2 : BitVec 32
  clientDataId2 : BitVec 16
  deriving DecidableEq, Repr

namespace ExecutionPrivateInformation2LegsMessage

def encode (message : ExecutionPrivateInformation2LegsMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 4 message.strategyTrdMatchId
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (CcpCode.encode message.ccpCode
    ++ (AggressorIndicator.encode message.aggressorIndicator
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 4 message.entryDate2
    ++ (encodeUIntLE 4 message.priority2
    ++ (encodeUIntLE 8 message.price2
    ++ (encodeUIntLE 4 message.displayQty2
    ++ (encodeUIntLE 4 message.orderId2
    ++ (encodeUIntLE 4 message.secondaryExecId2
    ++ (encodeUIntLE 4 message.orderQty2
    ++ (OrdStatus2.encode message.ordStatus2
    ++ (CcpCode2.encode message.ccpCode2
    ++ (AggressorIndicator2.encode message.aggressorIndicator2
    ++ (encodeUIntLE 4 message.requestId2
    ++ (encodeUIntLE 2 message.clientDataId2))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionPrivateInformation2LegsMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (strategyTrdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ccpCode, bytes) ← CcpCode.decode bytes
  let (aggressorIndicator, bytes) ← AggressorIndicator.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (entryDate2, bytes) ← decodeUIntLE 4 bytes
  let (priority2, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 8 bytes
  let (displayQty2, bytes) ← decodeUIntLE 4 bytes
  let (orderId2, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId2, bytes) ← decodeUIntLE 4 bytes
  let (orderQty2, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus2, bytes) ← OrdStatus2.decode bytes
  let (ccpCode2, bytes) ← CcpCode2.decode bytes
  let (aggressorIndicator2, bytes) ← AggressorIndicator2.decode bytes
  let (requestId2, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId2, bytes) ← decodeUIntLE 2 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, transactionCategory, strategyTrdMatchId, secondaryOrderId, entryDate, priority, price, displayQty, orderId, secondaryExecId, orderQty, ordStatus, ccpCode, aggressorIndicator, requestId, clientDataId, secondaryOrderId2, entryDate2, priority2, price2, displayQty2, orderId2, secondaryExecId2, orderQty2, ordStatus2, ccpCode2, aggressorIndicator2, requestId2, clientDataId2 }, bytes)

@[simp] theorem encode_length (message : ExecutionPrivateInformation2LegsMessage) : (encode message).length = 144 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, TransactionCategory.encode_length, OrdStatus.encode_length, CcpCode.encode_length, AggressorIndicator.encode_length, OrdStatus2.encode_length, CcpCode2.encode_length, AggressorIndicator2.encode_length]

theorem encode_length_pos (message : ExecutionPrivateInformation2LegsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionPrivateInformation2LegsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExecutionPrivateInformation2LegsMessage

/-- Trade Trade Amendment Or Cancellation 1 Leg Buy Private Information Message: 255 bytes -/
structure TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  transactionCategory : TransactionCategory
  strategyTrdMatchId : BitVec 32
  lastChangeFlag : BitVec 8
  bencrfptFlag : BencrfptFlag
  tradePriceCondition : TradePriceCondition
  preTradeTransparencyWaiver : PreTradeTransparencyWaiver
  deferralWaiver : DeferralWaiver
  postDeferralPublicationType : PostDeferralPublicationType
  publishDateAndTime : BitVec 64
  tradeDate : BitVec 64
  tradeSessionDate : BitVec 32
  amendedTradeType : AmendedTradeType
  execRefId : BitVec 32
  amendedTradeDate : BitVec 32
  broker : Alpha 4
  brokerTrader : Alpha 3
  brokerText : Alpha 15
  cancelPreAmendment : BitVec 8
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ccpCode : CcpCode
  aggressorIndicator : AggressorIndicator
  requestId : BitVec 32
  clientDataId : BitVec 16
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  persistence : Persistence
  selfMatchPreventionType : SelfMatchPreventionType
  member : Alpha 4
  trader : Alpha 3
  subMember : Alpha 1
  crossId : BitVec 32
  ccv : Alpha 20
  orderSecurityCode : BitVec 32
  externalMember : Alpha 4
  riskReduction : BitVec 8
  deriving DecidableEq, Repr

namespace TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage

def encode (message : TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 4 message.strategyTrdMatchId
    ++ (encodeUIntLE 1 message.lastChangeFlag
    ++ (BencrfptFlag.encode message.bencrfptFlag
    ++ (TradePriceCondition.encode message.tradePriceCondition
    ++ (PreTradeTransparencyWaiver.encode message.preTradeTransparencyWaiver
    ++ (DeferralWaiver.encode message.deferralWaiver
    ++ (PostDeferralPublicationType.encode message.postDeferralPublicationType
    ++ (encodeUIntLE 8 message.publishDateAndTime
    ++ (encodeUIntLE 8 message.tradeDate
    ++ (encodeUIntLE 4 message.tradeSessionDate
    ++ (AmendedTradeType.encode message.amendedTradeType
    ++ (encodeUIntLE 4 message.execRefId
    ++ (encodeUIntLE 4 message.amendedTradeDate
    ++ (Alpha.encode message.broker
    ++ (Alpha.encode message.brokerTrader
    ++ (Alpha.encode message.brokerText
    ++ (encodeUIntLE 1 message.cancelPreAmendment
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (CcpCode.encode message.ccpCode
    ++ (AggressorIndicator.encode message.aggressorIndicator
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (Persistence.encode message.persistence
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.member
    ++ (Alpha.encode message.trader
    ++ (Alpha.encode message.subMember
    ++ (encodeUIntLE 4 message.crossId
    ++ (Alpha.encode message.ccv
    ++ (encodeUIntLE 4 message.orderSecurityCode
    ++ (Alpha.encode message.externalMember
    ++ (encodeUIntLE 1 message.riskReduction)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (strategyTrdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (lastChangeFlag, bytes) ← decodeUIntLE 1 bytes
  let (bencrfptFlag, bytes) ← BencrfptFlag.decode bytes
  let (tradePriceCondition, bytes) ← TradePriceCondition.decode bytes
  let (preTradeTransparencyWaiver, bytes) ← PreTradeTransparencyWaiver.decode bytes
  let (deferralWaiver, bytes) ← DeferralWaiver.decode bytes
  let (postDeferralPublicationType, bytes) ← PostDeferralPublicationType.decode bytes
  let (publishDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 8 bytes
  let (tradeSessionDate, bytes) ← decodeUIntLE 4 bytes
  let (amendedTradeType, bytes) ← AmendedTradeType.decode bytes
  let (execRefId, bytes) ← decodeUIntLE 4 bytes
  let (amendedTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (broker, bytes) ← Alpha.decode 4 bytes
  let (brokerTrader, bytes) ← Alpha.decode 3 bytes
  let (brokerText, bytes) ← Alpha.decode 15 bytes
  let (cancelPreAmendment, bytes) ← decodeUIntLE 1 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ccpCode, bytes) ← CcpCode.decode bytes
  let (aggressorIndicator, bytes) ← AggressorIndicator.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (member, bytes) ← Alpha.decode 4 bytes
  let (trader, bytes) ← Alpha.decode 3 bytes
  let (subMember, bytes) ← Alpha.decode 1 bytes
  let (crossId, bytes) ← decodeUIntLE 4 bytes
  let (ccv, bytes) ← Alpha.decode 20 bytes
  let (orderSecurityCode, bytes) ← decodeUIntLE 4 bytes
  let (externalMember, bytes) ← Alpha.decode 4 bytes
  let (riskReduction, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, transactionCategory, strategyTrdMatchId, lastChangeFlag, bencrfptFlag, tradePriceCondition, preTradeTransparencyWaiver, deferralWaiver, postDeferralPublicationType, publishDateAndTime, tradeDate, tradeSessionDate, amendedTradeType, execRefId, amendedTradeDate, broker, brokerTrader, brokerText, cancelPreAmendment, secondaryOrderId, entryDate, priority, price, displayQty, orderId, secondaryExecId, orderQty, ordStatus, ccpCode, aggressorIndicator, requestId, clientDataId, algorithmicTradeIndicator, clientId, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, persistence, selfMatchPreventionType, member, trader, subMember, crossId, ccv, orderSecurityCode, externalMember, riskReduction }, bytes)

@[simp] theorem encode_length (message : TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage) : (encode message).length = 255 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, TransactionCategory.encode_length, BencrfptFlag.encode_length, TradePriceCondition.encode_length, PreTradeTransparencyWaiver.encode_length, DeferralWaiver.encode_length, PostDeferralPublicationType.encode_length, AmendedTradeType.encode_length, OrdStatus.encode_length, CcpCode.encode_length, AggressorIndicator.encode_length, LastCapacity.encode_length, Persistence.encode_length, SelfMatchPreventionType.encode_length]

theorem encode_length_pos (message : TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BencrfptFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreTradeTransparencyWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeferralWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PostDeferralPublicationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AmendedTradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage

/-- Trade Trade Amendment Or Cancellation 1 Leg Sell Private Information Message: 255 bytes -/
structure TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  transactionCategory : TransactionCategory
  strategyTrdMatchId : BitVec 32
  lastChangeFlag : BitVec 8
  bencrfptFlag : BencrfptFlag
  tradePriceCondition : TradePriceCondition
  preTradeTransparencyWaiver : PreTradeTransparencyWaiver
  deferralWaiver : DeferralWaiver
  postDeferralPublicationType : PostDeferralPublicationType
  publishDateAndTime : BitVec 64
  tradeDate : BitVec 64
  tradeSessionDate : BitVec 32
  amendedTradeType : AmendedTradeType
  execRefId : BitVec 32
  amendedTradeDate : BitVec 32
  broker : Alpha 4
  brokerTrader : Alpha 3
  brokerText : Alpha 15
  cancelPreAmendment : BitVec 8
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ccpCode : CcpCode
  aggressorIndicator : AggressorIndicator
  requestId : BitVec 32
  clientDataId : BitVec 16
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  persistence : Persistence
  selfMatchPreventionType : SelfMatchPreventionType
  member : Alpha 4
  trader : Alpha 3
  subMember : Alpha 1
  crossId : BitVec 32
  ccv : Alpha 20
  orderSecurityCode : BitVec 32
  externalMember : Alpha 4
  riskReduction : BitVec 8
  deriving DecidableEq, Repr

namespace TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage

def encode (message : TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 4 message.strategyTrdMatchId
    ++ (encodeUIntLE 1 message.lastChangeFlag
    ++ (BencrfptFlag.encode message.bencrfptFlag
    ++ (TradePriceCondition.encode message.tradePriceCondition
    ++ (PreTradeTransparencyWaiver.encode message.preTradeTransparencyWaiver
    ++ (DeferralWaiver.encode message.deferralWaiver
    ++ (PostDeferralPublicationType.encode message.postDeferralPublicationType
    ++ (encodeUIntLE 8 message.publishDateAndTime
    ++ (encodeUIntLE 8 message.tradeDate
    ++ (encodeUIntLE 4 message.tradeSessionDate
    ++ (AmendedTradeType.encode message.amendedTradeType
    ++ (encodeUIntLE 4 message.execRefId
    ++ (encodeUIntLE 4 message.amendedTradeDate
    ++ (Alpha.encode message.broker
    ++ (Alpha.encode message.brokerTrader
    ++ (Alpha.encode message.brokerText
    ++ (encodeUIntLE 1 message.cancelPreAmendment
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (CcpCode.encode message.ccpCode
    ++ (AggressorIndicator.encode message.aggressorIndicator
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (Persistence.encode message.persistence
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.member
    ++ (Alpha.encode message.trader
    ++ (Alpha.encode message.subMember
    ++ (encodeUIntLE 4 message.crossId
    ++ (Alpha.encode message.ccv
    ++ (encodeUIntLE 4 message.orderSecurityCode
    ++ (Alpha.encode message.externalMember
    ++ (encodeUIntLE 1 message.riskReduction)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (strategyTrdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (lastChangeFlag, bytes) ← decodeUIntLE 1 bytes
  let (bencrfptFlag, bytes) ← BencrfptFlag.decode bytes
  let (tradePriceCondition, bytes) ← TradePriceCondition.decode bytes
  let (preTradeTransparencyWaiver, bytes) ← PreTradeTransparencyWaiver.decode bytes
  let (deferralWaiver, bytes) ← DeferralWaiver.decode bytes
  let (postDeferralPublicationType, bytes) ← PostDeferralPublicationType.decode bytes
  let (publishDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 8 bytes
  let (tradeSessionDate, bytes) ← decodeUIntLE 4 bytes
  let (amendedTradeType, bytes) ← AmendedTradeType.decode bytes
  let (execRefId, bytes) ← decodeUIntLE 4 bytes
  let (amendedTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (broker, bytes) ← Alpha.decode 4 bytes
  let (brokerTrader, bytes) ← Alpha.decode 3 bytes
  let (brokerText, bytes) ← Alpha.decode 15 bytes
  let (cancelPreAmendment, bytes) ← decodeUIntLE 1 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ccpCode, bytes) ← CcpCode.decode bytes
  let (aggressorIndicator, bytes) ← AggressorIndicator.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (member, bytes) ← Alpha.decode 4 bytes
  let (trader, bytes) ← Alpha.decode 3 bytes
  let (subMember, bytes) ← Alpha.decode 1 bytes
  let (crossId, bytes) ← decodeUIntLE 4 bytes
  let (ccv, bytes) ← Alpha.decode 20 bytes
  let (orderSecurityCode, bytes) ← decodeUIntLE 4 bytes
  let (externalMember, bytes) ← Alpha.decode 4 bytes
  let (riskReduction, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, transactionCategory, strategyTrdMatchId, lastChangeFlag, bencrfptFlag, tradePriceCondition, preTradeTransparencyWaiver, deferralWaiver, postDeferralPublicationType, publishDateAndTime, tradeDate, tradeSessionDate, amendedTradeType, execRefId, amendedTradeDate, broker, brokerTrader, brokerText, cancelPreAmendment, secondaryOrderId, entryDate, priority, price, displayQty, orderId, secondaryExecId, orderQty, ordStatus, ccpCode, aggressorIndicator, requestId, clientDataId, algorithmicTradeIndicator, clientId, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, persistence, selfMatchPreventionType, member, trader, subMember, crossId, ccv, orderSecurityCode, externalMember, riskReduction }, bytes)

@[simp] theorem encode_length (message : TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage) : (encode message).length = 255 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, TransactionCategory.encode_length, BencrfptFlag.encode_length, TradePriceCondition.encode_length, PreTradeTransparencyWaiver.encode_length, DeferralWaiver.encode_length, PostDeferralPublicationType.encode_length, AmendedTradeType.encode_length, OrdStatus.encode_length, CcpCode.encode_length, AggressorIndicator.encode_length, LastCapacity.encode_length, Persistence.encode_length, SelfMatchPreventionType.encode_length]

theorem encode_length_pos (message : TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BencrfptFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreTradeTransparencyWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeferralWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PostDeferralPublicationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AmendedTradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage

/-- Trade Trade Amendment Or Cancellation 2 Legs Private Information Message: 398 bytes -/
structure TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  transactionCategory : TransactionCategory
  strategyTrdMatchId : BitVec 32
  lastChangeFlag : BitVec 8
  bencrfptFlag : BencrfptFlag
  tradePriceCondition : TradePriceCondition
  preTradeTransparencyWaiver : PreTradeTransparencyWaiver
  deferralWaiver : DeferralWaiver
  postDeferralPublicationType : PostDeferralPublicationType
  publishDateAndTime : BitVec 64
  tradeDate : BitVec 64
  tradeSessionDate : BitVec 32
  amendedTradeType : AmendedTradeType
  execRefId : BitVec 32
  amendedTradeDate : BitVec 32
  broker : Alpha 4
  brokerTrader : Alpha 3
  brokerText : Alpha 15
  cancelPreAmendment : BitVec 8
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ccpCode : CcpCode
  aggressorIndicator : AggressorIndicator
  requestId : BitVec 32
  clientDataId : BitVec 16
  algorithmicTradeIndicator : BitVec 8
  clientId : BitVec 32
  account : Alpha 5
  deaFlag : BitVec 8
  decisorId : BitVec 32
  executorId : BitVec 32
  liquidityProvisionActivity : BitVec 8
  giveInMember : Alpha 4
  firmMnemonic : Alpha 10
  allocText : Alpha 18
  lastCapacity : LastCapacity
  selfMatchPreventionId : BitVec 16
  persistence : Persistence
  selfMatchPreventionType : SelfMatchPreventionType
  member : Alpha 4
  trader : Alpha 3
  subMember : Alpha 1
  crossId : BitVec 32
  ccv : Alpha 20
  orderSecurityCode : BitVec 32
  externalMember : Alpha 4
  riskReduction : BitVec 8
  secondaryOrderId2 : BitVec 32
  entryDate2 : BitVec 32
  priority2 : BitVec 32
  price2 : BitVec 64
  displayQty2 : BitVec 32
  orderId2 : BitVec 32
  secondaryExecId2 : BitVec 32
  orderQty2 : BitVec 32
  ordStatus2 : OrdStatus2
  ccpCode2 : CcpCode2
  aggressorIndicator2 : AggressorIndicator2
  requestId2 : BitVec 32
  clientDataId2 : BitVec 16
  algorithmicTradeIndicator2 : BitVec 8
  clientId2 : BitVec 32
  account2 : Alpha 5
  deaFlag2 : BitVec 8
  decisorId2 : BitVec 32
  executorId2 : BitVec 32
  liquidityProvisionActivity2 : BitVec 8
  giveInMember2 : Alpha 4
  firmMnemonic2 : Alpha 10
  allocText2 : Alpha 18
  lastCapacity2 : LastCapacity2
  selfMatchPreventionId2 : BitVec 16
  persistence2 : Persistence2
  selfMatchPreventionType2 : SelfMatchPreventionType2
  member2 : Alpha 4
  trader2 : Alpha 3
  subMember2 : Alpha 1
  crossId2 : BitVec 32
  ccv2 : Alpha 20
  orderSecurityCode2 : BitVec 32
  externalMember2 : Alpha 4
  riskReduction2 : BitVec 8
  deriving DecidableEq, Repr

namespace TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage

def encode (message : TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 4 message.strategyTrdMatchId
    ++ (encodeUIntLE 1 message.lastChangeFlag
    ++ (BencrfptFlag.encode message.bencrfptFlag
    ++ (TradePriceCondition.encode message.tradePriceCondition
    ++ (PreTradeTransparencyWaiver.encode message.preTradeTransparencyWaiver
    ++ (DeferralWaiver.encode message.deferralWaiver
    ++ (PostDeferralPublicationType.encode message.postDeferralPublicationType
    ++ (encodeUIntLE 8 message.publishDateAndTime
    ++ (encodeUIntLE 8 message.tradeDate
    ++ (encodeUIntLE 4 message.tradeSessionDate
    ++ (AmendedTradeType.encode message.amendedTradeType
    ++ (encodeUIntLE 4 message.execRefId
    ++ (encodeUIntLE 4 message.amendedTradeDate
    ++ (Alpha.encode message.broker
    ++ (Alpha.encode message.brokerTrader
    ++ (Alpha.encode message.brokerText
    ++ (encodeUIntLE 1 message.cancelPreAmendment
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (CcpCode.encode message.ccpCode
    ++ (AggressorIndicator.encode message.aggressorIndicator
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 4 message.clientId
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.deaFlag
    ++ (encodeUIntLE 4 message.decisorId
    ++ (encodeUIntLE 4 message.executorId
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity
    ++ (Alpha.encode message.giveInMember
    ++ (Alpha.encode message.firmMnemonic
    ++ (Alpha.encode message.allocText
    ++ (LastCapacity.encode message.lastCapacity
    ++ (encodeUIntLE 2 message.selfMatchPreventionId
    ++ (Persistence.encode message.persistence
    ++ (SelfMatchPreventionType.encode message.selfMatchPreventionType
    ++ (Alpha.encode message.member
    ++ (Alpha.encode message.trader
    ++ (Alpha.encode message.subMember
    ++ (encodeUIntLE 4 message.crossId
    ++ (Alpha.encode message.ccv
    ++ (encodeUIntLE 4 message.orderSecurityCode
    ++ (Alpha.encode message.externalMember
    ++ (encodeUIntLE 1 message.riskReduction
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 4 message.entryDate2
    ++ (encodeUIntLE 4 message.priority2
    ++ (encodeUIntLE 8 message.price2
    ++ (encodeUIntLE 4 message.displayQty2
    ++ (encodeUIntLE 4 message.orderId2
    ++ (encodeUIntLE 4 message.secondaryExecId2
    ++ (encodeUIntLE 4 message.orderQty2
    ++ (OrdStatus2.encode message.ordStatus2
    ++ (CcpCode2.encode message.ccpCode2
    ++ (AggressorIndicator2.encode message.aggressorIndicator2
    ++ (encodeUIntLE 4 message.requestId2
    ++ (encodeUIntLE 2 message.clientDataId2
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator2
    ++ (encodeUIntLE 4 message.clientId2
    ++ (Alpha.encode message.account2
    ++ (encodeUIntLE 1 message.deaFlag2
    ++ (encodeUIntLE 4 message.decisorId2
    ++ (encodeUIntLE 4 message.executorId2
    ++ (encodeUIntLE 1 message.liquidityProvisionActivity2
    ++ (Alpha.encode message.giveInMember2
    ++ (Alpha.encode message.firmMnemonic2
    ++ (Alpha.encode message.allocText2
    ++ (LastCapacity2.encode message.lastCapacity2
    ++ (encodeUIntLE 2 message.selfMatchPreventionId2
    ++ (Persistence2.encode message.persistence2
    ++ (SelfMatchPreventionType2.encode message.selfMatchPreventionType2
    ++ (Alpha.encode message.member2
    ++ (Alpha.encode message.trader2
    ++ (Alpha.encode message.subMember2
    ++ (encodeUIntLE 4 message.crossId2
    ++ (Alpha.encode message.ccv2
    ++ (encodeUIntLE 4 message.orderSecurityCode2
    ++ (Alpha.encode message.externalMember2
    ++ (encodeUIntLE 1 message.riskReduction2))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (strategyTrdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (lastChangeFlag, bytes) ← decodeUIntLE 1 bytes
  let (bencrfptFlag, bytes) ← BencrfptFlag.decode bytes
  let (tradePriceCondition, bytes) ← TradePriceCondition.decode bytes
  let (preTradeTransparencyWaiver, bytes) ← PreTradeTransparencyWaiver.decode bytes
  let (deferralWaiver, bytes) ← DeferralWaiver.decode bytes
  let (postDeferralPublicationType, bytes) ← PostDeferralPublicationType.decode bytes
  let (publishDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 8 bytes
  let (tradeSessionDate, bytes) ← decodeUIntLE 4 bytes
  let (amendedTradeType, bytes) ← AmendedTradeType.decode bytes
  let (execRefId, bytes) ← decodeUIntLE 4 bytes
  let (amendedTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (broker, bytes) ← Alpha.decode 4 bytes
  let (brokerTrader, bytes) ← Alpha.decode 3 bytes
  let (brokerText, bytes) ← Alpha.decode 15 bytes
  let (cancelPreAmendment, bytes) ← decodeUIntLE 1 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ccpCode, bytes) ← CcpCode.decode bytes
  let (aggressorIndicator, bytes) ← AggressorIndicator.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (account, bytes) ← Alpha.decode 5 bytes
  let (deaFlag, bytes) ← decodeUIntLE 1 bytes
  let (decisorId, bytes) ← decodeUIntLE 4 bytes
  let (executorId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic, bytes) ← Alpha.decode 10 bytes
  let (allocText, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity, bytes) ← LastCapacity.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 2 bytes
  let (persistence, bytes) ← Persistence.decode bytes
  let (selfMatchPreventionType, bytes) ← SelfMatchPreventionType.decode bytes
  let (member, bytes) ← Alpha.decode 4 bytes
  let (trader, bytes) ← Alpha.decode 3 bytes
  let (subMember, bytes) ← Alpha.decode 1 bytes
  let (crossId, bytes) ← decodeUIntLE 4 bytes
  let (ccv, bytes) ← Alpha.decode 20 bytes
  let (orderSecurityCode, bytes) ← decodeUIntLE 4 bytes
  let (externalMember, bytes) ← Alpha.decode 4 bytes
  let (riskReduction, bytes) ← decodeUIntLE 1 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (entryDate2, bytes) ← decodeUIntLE 4 bytes
  let (priority2, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 8 bytes
  let (displayQty2, bytes) ← decodeUIntLE 4 bytes
  let (orderId2, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId2, bytes) ← decodeUIntLE 4 bytes
  let (orderQty2, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus2, bytes) ← OrdStatus2.decode bytes
  let (ccpCode2, bytes) ← CcpCode2.decode bytes
  let (aggressorIndicator2, bytes) ← AggressorIndicator2.decode bytes
  let (requestId2, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId2, bytes) ← decodeUIntLE 2 bytes
  let (algorithmicTradeIndicator2, bytes) ← decodeUIntLE 1 bytes
  let (clientId2, bytes) ← decodeUIntLE 4 bytes
  let (account2, bytes) ← Alpha.decode 5 bytes
  let (deaFlag2, bytes) ← decodeUIntLE 1 bytes
  let (decisorId2, bytes) ← decodeUIntLE 4 bytes
  let (executorId2, bytes) ← decodeUIntLE 4 bytes
  let (liquidityProvisionActivity2, bytes) ← decodeUIntLE 1 bytes
  let (giveInMember2, bytes) ← Alpha.decode 4 bytes
  let (firmMnemonic2, bytes) ← Alpha.decode 10 bytes
  let (allocText2, bytes) ← Alpha.decode 18 bytes
  let (lastCapacity2, bytes) ← LastCapacity2.decode bytes
  let (selfMatchPreventionId2, bytes) ← decodeUIntLE 2 bytes
  let (persistence2, bytes) ← Persistence2.decode bytes
  let (selfMatchPreventionType2, bytes) ← SelfMatchPreventionType2.decode bytes
  let (member2, bytes) ← Alpha.decode 4 bytes
  let (trader2, bytes) ← Alpha.decode 3 bytes
  let (subMember2, bytes) ← Alpha.decode 1 bytes
  let (crossId2, bytes) ← decodeUIntLE 4 bytes
  let (ccv2, bytes) ← Alpha.decode 20 bytes
  let (orderSecurityCode2, bytes) ← decodeUIntLE 4 bytes
  let (externalMember2, bytes) ← Alpha.decode 4 bytes
  let (riskReduction2, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, transactionCategory, strategyTrdMatchId, lastChangeFlag, bencrfptFlag, tradePriceCondition, preTradeTransparencyWaiver, deferralWaiver, postDeferralPublicationType, publishDateAndTime, tradeDate, tradeSessionDate, amendedTradeType, execRefId, amendedTradeDate, broker, brokerTrader, brokerText, cancelPreAmendment, secondaryOrderId, entryDate, priority, price, displayQty, orderId, secondaryExecId, orderQty, ordStatus, ccpCode, aggressorIndicator, requestId, clientDataId, algorithmicTradeIndicator, clientId, account, deaFlag, decisorId, executorId, liquidityProvisionActivity, giveInMember, firmMnemonic, allocText, lastCapacity, selfMatchPreventionId, persistence, selfMatchPreventionType, member, trader, subMember, crossId, ccv, orderSecurityCode, externalMember, riskReduction, secondaryOrderId2, entryDate2, priority2, price2, displayQty2, orderId2, secondaryExecId2, orderQty2, ordStatus2, ccpCode2, aggressorIndicator2, requestId2, clientDataId2, algorithmicTradeIndicator2, clientId2, account2, deaFlag2, decisorId2, executorId2, liquidityProvisionActivity2, giveInMember2, firmMnemonic2, allocText2, lastCapacity2, selfMatchPreventionId2, persistence2, selfMatchPreventionType2, member2, trader2, subMember2, crossId2, ccv2, orderSecurityCode2, externalMember2, riskReduction2 }, bytes)

@[simp] theorem encode_length (message : TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage) : (encode message).length = 398 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, TransactionCategory.encode_length, BencrfptFlag.encode_length, TradePriceCondition.encode_length, PreTradeTransparencyWaiver.encode_length, DeferralWaiver.encode_length, PostDeferralPublicationType.encode_length, AmendedTradeType.encode_length, OrdStatus.encode_length, CcpCode.encode_length, AggressorIndicator.encode_length, LastCapacity.encode_length, Persistence.encode_length, SelfMatchPreventionType.encode_length, OrdStatus2.encode_length, CcpCode2.encode_length, AggressorIndicator2.encode_length, LastCapacity2.encode_length, Persistence2.encode_length, SelfMatchPreventionType2.encode_length]

theorem encode_length_pos (message : TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BencrfptFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreTradeTransparencyWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeferralWaiver.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PostDeferralPublicationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AmendedTradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastCapacity2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Persistence2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SelfMatchPreventionType2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage

/-- Execution Private Information 1 Leg Buy Order Entry Message: 99 bytes -/
structure ExecutionPrivateInformation1LegBuyOrderEntryMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  transactionCategory : TransactionCategory
  strategyTrdMatchId : BitVec 32
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ccpCode : CcpCode
  aggressorIndicator : AggressorIndicator
  requestId : BitVec 32
  clientDataId : BitVec 16
  deriving DecidableEq, Repr

namespace ExecutionPrivateInformation1LegBuyOrderEntryMessage

def encode (message : ExecutionPrivateInformation1LegBuyOrderEntryMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 4 message.strategyTrdMatchId
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (CcpCode.encode message.ccpCode
    ++ (AggressorIndicator.encode message.aggressorIndicator
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionPrivateInformation1LegBuyOrderEntryMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (strategyTrdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ccpCode, bytes) ← CcpCode.decode bytes
  let (aggressorIndicator, bytes) ← AggressorIndicator.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, transactionCategory, strategyTrdMatchId, secondaryOrderId, entryDate, priority, price, displayQty, orderId, secondaryExecId, orderQty, ordStatus, ccpCode, aggressorIndicator, requestId, clientDataId }, bytes)

@[simp] theorem encode_length (message : ExecutionPrivateInformation1LegBuyOrderEntryMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, TransactionCategory.encode_length, OrdStatus.encode_length, CcpCode.encode_length, AggressorIndicator.encode_length]

theorem encode_length_pos (message : ExecutionPrivateInformation1LegBuyOrderEntryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionPrivateInformation1LegBuyOrderEntryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExecutionPrivateInformation1LegBuyOrderEntryMessage

/-- Execution Private Information 1 Leg Sell Order Entry Message: 99 bytes -/
structure ExecutionPrivateInformation1LegSellOrderEntryMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  marketSegmentId : Alpha 4
  tradingSessionId : BitVec 8
  trdMatchId : BitVec 32
  tradeType : TradeType
  lastPx : BitVec 64
  lastQty : BitVec 32
  grossTradeAmt : BitVec 64
  designation : Designation
  marketMechanism : MarketMechanism
  algoFlag : BitVec 8
  transactionCategory : TransactionCategory
  strategyTrdMatchId : BitVec 32
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  orderId : BitVec 32
  secondaryExecId : BitVec 32
  orderQty : BitVec 32
  ordStatus : OrdStatus
  ccpCode : CcpCode
  aggressorIndicator : AggressorIndicator
  requestId : BitVec 32
  clientDataId : BitVec 16
  deriving DecidableEq, Repr

namespace ExecutionPrivateInformation1LegSellOrderEntryMessage

def encode (message : ExecutionPrivateInformation1LegSellOrderEntryMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (Alpha.encode message.marketSegmentId
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (Designation.encode message.designation
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (encodeUIntLE 1 message.algoFlag
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (encodeUIntLE 4 message.strategyTrdMatchId
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.orderId
    ++ (encodeUIntLE 4 message.secondaryExecId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (CcpCode.encode message.ccpCode
    ++ (AggressorIndicator.encode message.aggressorIndicator
    ++ (encodeUIntLE 4 message.requestId
    ++ (encodeUIntLE 2 message.clientDataId)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionPrivateInformation1LegSellOrderEntryMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (designation, bytes) ← Designation.decode bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (algoFlag, bytes) ← decodeUIntLE 1 bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (strategyTrdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ccpCode, bytes) ← CcpCode.decode bytes
  let (aggressorIndicator, bytes) ← AggressorIndicator.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (clientDataId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, transactionCategory, strategyTrdMatchId, secondaryOrderId, entryDate, priority, price, displayQty, orderId, secondaryExecId, orderQty, ordStatus, ccpCode, aggressorIndicator, requestId, clientDataId }, bytes)

@[simp] theorem encode_length (message : ExecutionPrivateInformation1LegSellOrderEntryMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, TransactionCategory.encode_length, OrdStatus.encode_length, CcpCode.encode_length, AggressorIndicator.encode_length]

theorem encode_length_pos (message : ExecutionPrivateInformation1LegSellOrderEntryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionPrivateInformation1LegSellOrderEntryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Designation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExecutionPrivateInformation1LegSellOrderEntryMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | logonResponseMessage (message : LogonResponseMessage) -- 8
  | logoutResponseMessage (message : LogoutResponseMessage) -- 11
  | heartbeatMessage (message : HeartbeatMessage) -- 48
  | networkStatusMessage (message : NetworkStatusMessage) -- 10
  | logonMessage (message : LogonMessage) -- 65
  | rejectMessage (message : RejectMessage) -- 13
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 104
  | newsMessage (message : NewsMessage) -- 66
  | securityListCancellationReportMessage (message : SecurityListCancellationReportMessage) -- 120
  | statisticsMessage (message : StatisticsMessage) -- 132
  | securityListMessage (message : SecurityListMessage) -- 121
  | securityListUpdateReportMessage (message : SecurityListUpdateReportMessage) -- 128
  | securityStatusMessage (message : SecurityStatusMessage) -- 102
  | familyStatusMessage (message : FamilyStatusMessage) -- 137
  | orderCancellationMarketMemberMessage (message : OrderCancellationMarketMemberMessage) -- 1
  | quoteCancellationMarketMemberMessage (message : QuoteCancellationMarketMemberMessage) -- 5
  | indicationOfInterestMessage (message : IndicationOfInterestMessage) -- 54
  | orderAndQuoteClientDataMessage (message : OrderAndQuoteClientDataMessage) -- 111
  | deltaProtectionParametersMessage (message : DeltaProtectionParametersMessage) -- 134
  | simpleNewOrderMessage (message : SimpleNewOrderMessage) -- 68
  | simpleNewOrderWithClientDataMessage (message : SimpleNewOrderWithClientDataMessage) -- 69
  | simpleOrderModificationMessage (message : SimpleOrderModificationMessage) -- 71
  | simpleOrderModificationWithClientDataMessage (message : SimpleOrderModificationWithClientDataMessage) -- 72
  | orderCancellationRequestMessage (message : OrderCancellationRequestMessage) -- 70
  | newQuoteMessage (message : NewQuoteMessage) -- 83
  | quoteModificationRequestMessage (message : QuoteModificationRequestMessage) -- 97
  | quoteCancellationRequestMessage (message : QuoteCancellationRequestMessage) -- 90
  | massOrderquoteCancellationMessage (message : MassOrderquoteCancellationMessage) -- 113
  | orderAndQuoteClientDataParametersAckNackMessage (message : OrderAndQuoteClientDataParametersAckNackMessage) -- 135
  | deltaProtectionParametersAckNackMessage (message : DeltaProtectionParametersAckNackMessage) -- 136
  | simpleOrderStatusMessage (message : SimpleOrderStatusMessage) -- 2
  | quoteStatusMessage (message : QuoteStatusMessage) -- 6
  | orderCancelRejectMessage (message : OrderCancelRejectMessage) -- 57
  | massOrderquoteCancellationCompletionMessage (message : MassOrderquoteCancellationCompletionMessage) -- 114
  | massOrderquoteCancellationRejectMessage (message : MassOrderquoteCancellationRejectMessage) -- 115
  | businessMessageRejectMessage (message : BusinessMessageRejectMessage) -- 106
  | executionPrivateInformation2LegsMessage (message : ExecutionPrivateInformation2LegsMessage) -- 23
  | tradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage (message : TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage) -- 26
  | tradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage (message : TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage) -- 28
  | tradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage (message : TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage) -- 30
  | executionPrivateInformation1LegBuyOrderEntryMessage (message : ExecutionPrivateInformation1LegBuyOrderEntryMessage) -- 18
  | executionPrivateInformation1LegSellOrderEntryMessage (message : ExecutionPrivateInformation1LegSellOrderEntryMessage) -- 20
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .logonResponseMessage _ => 8
  | .logoutResponseMessage _ => 11
  | .heartbeatMessage _ => 48
  | .networkStatusMessage _ => 10
  | .logonMessage _ => 65
  | .rejectMessage _ => 13
  | .tradingSessionStatusMessage _ => 104
  | .newsMessage _ => 66
  | .securityListCancellationReportMessage _ => 120
  | .statisticsMessage _ => 132
  | .securityListMessage _ => 121
  | .securityListUpdateReportMessage _ => 128
  | .securityStatusMessage _ => 102
  | .familyStatusMessage _ => 137
  | .orderCancellationMarketMemberMessage _ => 1
  | .quoteCancellationMarketMemberMessage _ => 5
  | .indicationOfInterestMessage _ => 54
  | .orderAndQuoteClientDataMessage _ => 111
  | .deltaProtectionParametersMessage _ => 134
  | .simpleNewOrderMessage _ => 68
  | .simpleNewOrderWithClientDataMessage _ => 69
  | .simpleOrderModificationMessage _ => 71
  | .simpleOrderModificationWithClientDataMessage _ => 72
  | .orderCancellationRequestMessage _ => 70
  | .newQuoteMessage _ => 83
  | .quoteModificationRequestMessage _ => 97
  | .quoteCancellationRequestMessage _ => 90
  | .massOrderquoteCancellationMessage _ => 113
  | .orderAndQuoteClientDataParametersAckNackMessage _ => 135
  | .deltaProtectionParametersAckNackMessage _ => 136
  | .simpleOrderStatusMessage _ => 2
  | .quoteStatusMessage _ => 6
  | .orderCancelRejectMessage _ => 57
  | .massOrderquoteCancellationCompletionMessage _ => 114
  | .massOrderquoteCancellationRejectMessage _ => 115
  | .businessMessageRejectMessage _ => 106
  | .executionPrivateInformation2LegsMessage _ => 23
  | .tradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage _ => 26
  | .tradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage _ => 28
  | .tradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage _ => 30
  | .executionPrivateInformation1LegBuyOrderEntryMessage _ => 18
  | .executionPrivateInformation1LegSellOrderEntryMessage _ => 20

def encode : Payload → List UInt8
  | .logonResponseMessage message => LogonResponseMessage.encode message
  | .logoutResponseMessage message => LogoutResponseMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .networkStatusMessage message => NetworkStatusMessage.encode message
  | .logonMessage message => LogonMessage.encode message
  | .rejectMessage message => RejectMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .newsMessage message => NewsMessage.encode message
  | .securityListCancellationReportMessage message => SecurityListCancellationReportMessage.encode message
  | .statisticsMessage message => StatisticsMessage.encode message
  | .securityListMessage message => SecurityListMessage.encode message
  | .securityListUpdateReportMessage message => SecurityListUpdateReportMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .familyStatusMessage message => FamilyStatusMessage.encode message
  | .orderCancellationMarketMemberMessage message => OrderCancellationMarketMemberMessage.encode message
  | .quoteCancellationMarketMemberMessage message => QuoteCancellationMarketMemberMessage.encode message
  | .indicationOfInterestMessage message => IndicationOfInterestMessage.encode message
  | .orderAndQuoteClientDataMessage message => OrderAndQuoteClientDataMessage.encode message
  | .deltaProtectionParametersMessage message => DeltaProtectionParametersMessage.encode message
  | .simpleNewOrderMessage message => SimpleNewOrderMessage.encode message
  | .simpleNewOrderWithClientDataMessage message => SimpleNewOrderWithClientDataMessage.encode message
  | .simpleOrderModificationMessage message => SimpleOrderModificationMessage.encode message
  | .simpleOrderModificationWithClientDataMessage message => SimpleOrderModificationWithClientDataMessage.encode message
  | .orderCancellationRequestMessage message => OrderCancellationRequestMessage.encode message
  | .newQuoteMessage message => NewQuoteMessage.encode message
  | .quoteModificationRequestMessage message => QuoteModificationRequestMessage.encode message
  | .quoteCancellationRequestMessage message => QuoteCancellationRequestMessage.encode message
  | .massOrderquoteCancellationMessage message => MassOrderquoteCancellationMessage.encode message
  | .orderAndQuoteClientDataParametersAckNackMessage message => OrderAndQuoteClientDataParametersAckNackMessage.encode message
  | .deltaProtectionParametersAckNackMessage message => DeltaProtectionParametersAckNackMessage.encode message
  | .simpleOrderStatusMessage message => SimpleOrderStatusMessage.encode message
  | .quoteStatusMessage message => QuoteStatusMessage.encode message
  | .orderCancelRejectMessage message => OrderCancelRejectMessage.encode message
  | .massOrderquoteCancellationCompletionMessage message => MassOrderquoteCancellationCompletionMessage.encode message
  | .massOrderquoteCancellationRejectMessage message => MassOrderquoteCancellationRejectMessage.encode message
  | .businessMessageRejectMessage message => BusinessMessageRejectMessage.encode message
  | .executionPrivateInformation2LegsMessage message => ExecutionPrivateInformation2LegsMessage.encode message
  | .tradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage message => TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage.encode message
  | .tradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage message => TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage.encode message
  | .tradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage message => TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage.encode message
  | .executionPrivateInformation1LegBuyOrderEntryMessage message => ExecutionPrivateInformation1LegBuyOrderEntryMessage.encode message
  | .executionPrivateInformation1LegSellOrderEntryMessage message => ExecutionPrivateInformation1LegSellOrderEntryMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 713 := by
  cases message with
  | logonResponseMessage inner =>
    simp only [encode, LogonResponseMessage.encode_length]
    omega
  | logoutResponseMessage inner =>
    simp only [encode, LogoutResponseMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | networkStatusMessage inner =>
    simp only [encode, NetworkStatusMessage.encode_length]
    omega
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [encode, RejectMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [encode, TradingSessionStatusMessage.encode_length]
    omega
  | newsMessage inner =>
    simp only [encode, NewsMessage.encode_length]
    omega
  | securityListCancellationReportMessage inner =>
    simp only [encode, SecurityListCancellationReportMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [encode, StatisticsMessage.encode_length]
    omega
  | securityListMessage inner =>
    simp only [encode, SecurityListMessage.encode_length]
    omega
  | securityListUpdateReportMessage inner =>
    simp only [encode, SecurityListUpdateReportMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | familyStatusMessage inner =>
    simp only [encode, FamilyStatusMessage.encode_length]
    omega
  | orderCancellationMarketMemberMessage inner =>
    simp only [encode, OrderCancellationMarketMemberMessage.encode_length]
    omega
  | quoteCancellationMarketMemberMessage inner =>
    simp only [encode, QuoteCancellationMarketMemberMessage.encode_length]
    omega
  | indicationOfInterestMessage inner =>
    simp only [encode, IndicationOfInterestMessage.encode_length]
    omega
  | orderAndQuoteClientDataMessage inner =>
    simp only [encode, OrderAndQuoteClientDataMessage.encode_length]
    omega
  | deltaProtectionParametersMessage inner =>
    simp only [encode, DeltaProtectionParametersMessage.encode_length]
    omega
  | simpleNewOrderMessage inner =>
    simp only [encode, SimpleNewOrderMessage.encode_length]
    omega
  | simpleNewOrderWithClientDataMessage inner =>
    simp only [encode, SimpleNewOrderWithClientDataMessage.encode_length]
    omega
  | simpleOrderModificationMessage inner =>
    simp only [encode, SimpleOrderModificationMessage.encode_length]
    omega
  | simpleOrderModificationWithClientDataMessage inner =>
    simp only [encode, SimpleOrderModificationWithClientDataMessage.encode_length]
    omega
  | orderCancellationRequestMessage inner =>
    simp only [encode, OrderCancellationRequestMessage.encode_length]
    omega
  | newQuoteMessage inner =>
    simp only [encode, NewQuoteMessage.encode_length]
    omega
  | quoteModificationRequestMessage inner =>
    simp only [encode, QuoteModificationRequestMessage.encode_length]
    omega
  | quoteCancellationRequestMessage inner =>
    simp only [encode, QuoteCancellationRequestMessage.encode_length]
    omega
  | massOrderquoteCancellationMessage inner =>
    simp only [encode, MassOrderquoteCancellationMessage.encode_length]
    omega
  | orderAndQuoteClientDataParametersAckNackMessage inner =>
    simp only [encode, OrderAndQuoteClientDataParametersAckNackMessage.encode_length]
    omega
  | deltaProtectionParametersAckNackMessage inner =>
    simp only [encode, DeltaProtectionParametersAckNackMessage.encode_length]
    omega
  | simpleOrderStatusMessage inner =>
    simp only [encode, SimpleOrderStatusMessage.encode_length]
    omega
  | quoteStatusMessage inner =>
    simp only [encode, QuoteStatusMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [encode, OrderCancelRejectMessage.encode_length]
    omega
  | massOrderquoteCancellationCompletionMessage inner =>
    simp only [encode, MassOrderquoteCancellationCompletionMessage.encode_length]
    omega
  | massOrderquoteCancellationRejectMessage inner =>
    simp only [encode, MassOrderquoteCancellationRejectMessage.encode_length]
    omega
  | businessMessageRejectMessage inner =>
    simp only [encode, BusinessMessageRejectMessage.encode_length]
    omega
  | executionPrivateInformation2LegsMessage inner =>
    simp only [encode, ExecutionPrivateInformation2LegsMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage inner =>
    simp only [encode, TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage inner =>
    simp only [encode, TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage inner =>
    simp only [encode, TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage.encode_length]
    omega
  | executionPrivateInformation1LegBuyOrderEntryMessage inner =>
    simp only [encode, ExecutionPrivateInformation1LegBuyOrderEntryMessage.encode_length]
    omega
  | executionPrivateInformation1LegSellOrderEntryMessage inner =>
    simp only [encode, ExecutionPrivateInformation1LegSellOrderEntryMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 8 then (LogonResponseMessage.decode bytes).map fun (message, rest) => (.logonResponseMessage message, rest)
  else if tag = 11 then (LogoutResponseMessage.decode bytes).map fun (message, rest) => (.logoutResponseMessage message, rest)
  else if tag = 48 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 10 then (NetworkStatusMessage.decode bytes).map fun (message, rest) => (.networkStatusMessage message, rest)
  else if tag = 65 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 13 then (RejectMessage.decode bytes).map fun (message, rest) => (.rejectMessage message, rest)
  else if tag = 104 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 66 then (NewsMessage.decode bytes).map fun (message, rest) => (.newsMessage message, rest)
  else if tag = 120 then (SecurityListCancellationReportMessage.decode bytes).map fun (message, rest) => (.securityListCancellationReportMessage message, rest)
  else if tag = 132 then (StatisticsMessage.decode bytes).map fun (message, rest) => (.statisticsMessage message, rest)
  else if tag = 121 then (SecurityListMessage.decode bytes).map fun (message, rest) => (.securityListMessage message, rest)
  else if tag = 128 then (SecurityListUpdateReportMessage.decode bytes).map fun (message, rest) => (.securityListUpdateReportMessage message, rest)
  else if tag = 102 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 137 then (FamilyStatusMessage.decode bytes).map fun (message, rest) => (.familyStatusMessage message, rest)
  else if tag = 1 then (OrderCancellationMarketMemberMessage.decode bytes).map fun (message, rest) => (.orderCancellationMarketMemberMessage message, rest)
  else if tag = 5 then (QuoteCancellationMarketMemberMessage.decode bytes).map fun (message, rest) => (.quoteCancellationMarketMemberMessage message, rest)
  else if tag = 54 then (IndicationOfInterestMessage.decode bytes).map fun (message, rest) => (.indicationOfInterestMessage message, rest)
  else if tag = 111 then (OrderAndQuoteClientDataMessage.decode bytes).map fun (message, rest) => (.orderAndQuoteClientDataMessage message, rest)
  else if tag = 134 then (DeltaProtectionParametersMessage.decode bytes).map fun (message, rest) => (.deltaProtectionParametersMessage message, rest)
  else if tag = 68 then (SimpleNewOrderMessage.decode bytes).map fun (message, rest) => (.simpleNewOrderMessage message, rest)
  else if tag = 69 then (SimpleNewOrderWithClientDataMessage.decode bytes).map fun (message, rest) => (.simpleNewOrderWithClientDataMessage message, rest)
  else if tag = 71 then (SimpleOrderModificationMessage.decode bytes).map fun (message, rest) => (.simpleOrderModificationMessage message, rest)
  else if tag = 72 then (SimpleOrderModificationWithClientDataMessage.decode bytes).map fun (message, rest) => (.simpleOrderModificationWithClientDataMessage message, rest)
  else if tag = 70 then (OrderCancellationRequestMessage.decode bytes).map fun (message, rest) => (.orderCancellationRequestMessage message, rest)
  else if tag = 83 then (NewQuoteMessage.decode bytes).map fun (message, rest) => (.newQuoteMessage message, rest)
  else if tag = 97 then (QuoteModificationRequestMessage.decode bytes).map fun (message, rest) => (.quoteModificationRequestMessage message, rest)
  else if tag = 90 then (QuoteCancellationRequestMessage.decode bytes).map fun (message, rest) => (.quoteCancellationRequestMessage message, rest)
  else if tag = 113 then (MassOrderquoteCancellationMessage.decode bytes).map fun (message, rest) => (.massOrderquoteCancellationMessage message, rest)
  else if tag = 135 then (OrderAndQuoteClientDataParametersAckNackMessage.decode bytes).map fun (message, rest) => (.orderAndQuoteClientDataParametersAckNackMessage message, rest)
  else if tag = 136 then (DeltaProtectionParametersAckNackMessage.decode bytes).map fun (message, rest) => (.deltaProtectionParametersAckNackMessage message, rest)
  else if tag = 2 then (SimpleOrderStatusMessage.decode bytes).map fun (message, rest) => (.simpleOrderStatusMessage message, rest)
  else if tag = 6 then (QuoteStatusMessage.decode bytes).map fun (message, rest) => (.quoteStatusMessage message, rest)
  else if tag = 57 then (OrderCancelRejectMessage.decode bytes).map fun (message, rest) => (.orderCancelRejectMessage message, rest)
  else if tag = 114 then (MassOrderquoteCancellationCompletionMessage.decode bytes).map fun (message, rest) => (.massOrderquoteCancellationCompletionMessage message, rest)
  else if tag = 115 then (MassOrderquoteCancellationRejectMessage.decode bytes).map fun (message, rest) => (.massOrderquoteCancellationRejectMessage message, rest)
  else if tag = 106 then (BusinessMessageRejectMessage.decode bytes).map fun (message, rest) => (.businessMessageRejectMessage message, rest)
  else if tag = 23 then (ExecutionPrivateInformation2LegsMessage.decode bytes).map fun (message, rest) => (.executionPrivateInformation2LegsMessage message, rest)
  else if tag = 26 then (TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage.decode bytes).map fun (message, rest) => (.tradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage message, rest)
  else if tag = 28 then (TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage.decode bytes).map fun (message, rest) => (.tradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage message, rest)
  else if tag = 30 then (TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage.decode bytes).map fun (message, rest) => (.tradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage message, rest)
  else if tag = 18 then (ExecutionPrivateInformation1LegBuyOrderEntryMessage.decode bytes).map fun (message, rest) => (.executionPrivateInformation1LegBuyOrderEntryMessage message, rest)
  else if tag = 20 then (ExecutionPrivateInformation1LegSellOrderEntryMessage.decode bytes).map fun (message, rest) => (.executionPrivateInformation1LegSellOrderEntryMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | logonResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogonResponseMessage.encode_length]
    omega
  | logoutResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogoutResponseMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, HeartbeatMessage.encode_length]
    omega
  | networkStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NetworkStatusMessage.encode_length]
    omega
  | logonMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogonMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RejectMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingSessionStatusMessage.encode_length]
    omega
  | newsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NewsMessage.encode_length]
    omega
  | securityListCancellationReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityListCancellationReportMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsMessage.encode_length]
    omega
  | securityListMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityListMessage.encode_length]
    omega
  | securityListUpdateReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityListUpdateReportMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityStatusMessage.encode_length]
    omega
  | familyStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, FamilyStatusMessage.encode_length]
    omega
  | orderCancellationMarketMemberMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancellationMarketMemberMessage.encode_length]
    omega
  | quoteCancellationMarketMemberMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteCancellationMarketMemberMessage.encode_length]
    omega
  | indicationOfInterestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndicationOfInterestMessage.encode_length]
    omega
  | orderAndQuoteClientDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderAndQuoteClientDataMessage.encode_length]
    omega
  | deltaProtectionParametersMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, DeltaProtectionParametersMessage.encode_length]
    omega
  | simpleNewOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SimpleNewOrderMessage.encode_length]
    omega
  | simpleNewOrderWithClientDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SimpleNewOrderWithClientDataMessage.encode_length]
    omega
  | simpleOrderModificationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SimpleOrderModificationMessage.encode_length]
    omega
  | simpleOrderModificationWithClientDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SimpleOrderModificationWithClientDataMessage.encode_length]
    omega
  | orderCancellationRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancellationRequestMessage.encode_length]
    omega
  | newQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NewQuoteMessage.encode_length]
    omega
  | quoteModificationRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteModificationRequestMessage.encode_length]
    omega
  | quoteCancellationRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteCancellationRequestMessage.encode_length]
    omega
  | massOrderquoteCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MassOrderquoteCancellationMessage.encode_length]
    omega
  | orderAndQuoteClientDataParametersAckNackMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderAndQuoteClientDataParametersAckNackMessage.encode_length]
    omega
  | deltaProtectionParametersAckNackMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, DeltaProtectionParametersAckNackMessage.encode_length]
    omega
  | simpleOrderStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SimpleOrderStatusMessage.encode_length]
    omega
  | quoteStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteStatusMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancelRejectMessage.encode_length]
    omega
  | massOrderquoteCancellationCompletionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MassOrderquoteCancellationCompletionMessage.encode_length]
    omega
  | massOrderquoteCancellationRejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MassOrderquoteCancellationRejectMessage.encode_length]
    omega
  | businessMessageRejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BusinessMessageRejectMessage.encode_length]
    omega
  | executionPrivateInformation2LegsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExecutionPrivateInformation2LegsMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage.encode_length]
    omega
  | executionPrivateInformation1LegBuyOrderEntryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExecutionPrivateInformation1LegBuyOrderEntryMessage.encode_length]
    omega
  | executionPrivateInformation1LegSellOrderEntryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExecutionPrivateInformation1LegSellOrderEntryMessage.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
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

end Omi.BmeMeffOrderentryBmegateV16
