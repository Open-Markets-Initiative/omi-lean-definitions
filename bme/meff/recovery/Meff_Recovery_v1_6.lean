import Wire

/-!
# Bolsas y Mercados Españoles MEFF Recovery v1.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BmeMeffRecoveryBmegateV16

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
  text : Alpha 58
  msgRejectedReference : Alpha 7
  deriving DecidableEq, Repr

namespace RejectMessage

def encode (message : RejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 1 message.sessionRejectReason
    ++ (Alpha.encode message.text
    ++ (Alpha.encode message.msgRejectedReference)))

def decode (bytes : List UInt8) : Option (RejectMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sessionRejectReason, bytes) ← decodeUIntLE 1 bytes
  let (text, bytes) ← Alpha.decode 58 bytes
  let (msgRejectedReference, bytes) ← Alpha.decode 7 bytes
  pure ({ sequenceNumber, sessionRejectReason, text, msgRejectedReference }, bytes)

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

/-- Order Book Clear Message: 16 bytes -/
structure OrderBookClearMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  deriving DecidableEq, Repr

namespace OrderBookClearMessage

def encode (message : OrderBookClearMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime))

def decode (bytes : List UInt8) : Option (OrderBookClearMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime }, bytes)

@[simp] theorem encode_length (message : OrderBookClearMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderBookClearMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookClearMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderBookClearMessage

/-- Order Market Pre Transparency Information Message: 42 bytes -/
structure OrderMarketPreTransparencyInformationMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  secondaryOrderId : BitVec 32
  entryDate : BitVec 32
  side : Side
  priority : BitVec 32
  price : BitVec 64
  displayQty : BitVec 32
  retailClFlag : BitVec 8
  deriving DecidableEq, Repr

namespace OrderMarketPreTransparencyInformationMessage

def encode (message : OrderMarketPreTransparencyInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 4 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.entryDate
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.priority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 1 message.retailClFlag)))))))))

def decode (bytes : List UInt8) : Option (OrderMarketPreTransparencyInformationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 4 bytes
  let (entryDate, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (priority, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (retailClFlag, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, entryDate, side, priority, price, displayQty, retailClFlag }, bytes)

@[simp] theorem encode_length (message : OrderMarketPreTransparencyInformationMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length]

theorem encode_length_pos (message : OrderMarketPreTransparencyInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMarketPreTransparencyInformationMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderMarketPreTransparencyInformationMessage

/-- Quote Market Pre Transparency Information Message: 56 bytes -/
structure QuoteMarketPreTransparencyInformationMessage where
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
  deriving DecidableEq, Repr

namespace QuoteMarketPreTransparencyInformationMessage

def encode (message : QuoteMarketPreTransparencyInformationMessage) : List UInt8 :=
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
    ++ (encodeUIntLE 4 message.displayQty2))))))))))

def decode (bytes : List UInt8) : Option (QuoteMarketPreTransparencyInformationMessage × List UInt8) := do
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
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, secondaryOrderId, secondaryOrderId2, priority, price, displayQty, priority2, price2, displayQty2 }, bytes)

@[simp] theorem encode_length (message : QuoteMarketPreTransparencyInformationMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteMarketPreTransparencyInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteMarketPreTransparencyInformationMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteMarketPreTransparencyInformationMessage

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

/-- Trade Market Post Transparency Information Topofbook Message: 54 bytes -/
structure TradeMarketPostTransparencyInformationTopofbookMessage where
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
  deriving DecidableEq, Repr

namespace TradeMarketPostTransparencyInformationTopofbookMessage

def encode (message : TradeMarketPostTransparencyInformationTopofbookMessage) : List UInt8 :=
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
    ++ (encodeUIntLE 4 message.strategyTrdMatchId))))))))))))))

def decode (bytes : List UInt8) : Option (TradeMarketPostTransparencyInformationTopofbookMessage × List UInt8) := do
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
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, transactionCategory, strategyTrdMatchId }, bytes)

@[simp] theorem encode_length (message : TradeMarketPostTransparencyInformationTopofbookMessage) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, TransactionCategory.encode_length]

theorem encode_length_pos (message : TradeMarketPostTransparencyInformationTopofbookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMarketPostTransparencyInformationTopofbookMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMarketPostTransparencyInformationTopofbookMessage

/-- Trade Trade Amendment Or Cancellation Message: 89 bytes -/
structure TradeTradeAmendmentOrCancellationMessage where
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
  deriving DecidableEq, Repr

namespace TradeTradeAmendmentOrCancellationMessage

def encode (message : TradeTradeAmendmentOrCancellationMessage) : List UInt8 :=
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
    ++ (encodeUIntLE 4 message.amendedTradeDate))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeTradeAmendmentOrCancellationMessage × List UInt8) := do
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
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, transactionCategory, strategyTrdMatchId, lastChangeFlag, bencrfptFlag, tradePriceCondition, preTradeTransparencyWaiver, deferralWaiver, postDeferralPublicationType, publishDateAndTime, tradeDate, tradeSessionDate, amendedTradeType, execRefId, amendedTradeDate }, bytes)

@[simp] theorem encode_length (message : TradeTradeAmendmentOrCancellationMessage) : (encode message).length = 89 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, TransactionCategory.encode_length, BencrfptFlag.encode_length, TradePriceCondition.encode_length, PreTradeTransparencyWaiver.encode_length, DeferralWaiver.encode_length, PostDeferralPublicationType.encode_length, AmendedTradeType.encode_length]

theorem encode_length_pos (message : TradeTradeAmendmentOrCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeTradeAmendmentOrCancellationMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeTradeAmendmentOrCancellationMessage

/-- Trade Market Post Transparency Information Full Depth Message: 104 bytes -/
structure TradeMarketPostTransparencyInformationFullDepthMessage where
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
  retailClFlag : BitVec 8
  secondaryOrderId2 : BitVec 32
  entryDate2 : BitVec 32
  priority2 : BitVec 32
  price2 : BitVec 64
  displayQty2 : BitVec 32
  retailClFlag2 : BitVec 8
  deriving DecidableEq, Repr

namespace TradeMarketPostTransparencyInformationFullDepthMessage

def encode (message : TradeMarketPostTransparencyInformationFullDepthMessage) : List UInt8 :=
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
    ++ (encodeUIntLE 1 message.retailClFlag
    ++ (encodeUIntLE 4 message.secondaryOrderId2
    ++ (encodeUIntLE 4 message.entryDate2
    ++ (encodeUIntLE 4 message.priority2
    ++ (encodeUIntLE 8 message.price2
    ++ (encodeUIntLE 4 message.displayQty2
    ++ (encodeUIntLE 1 message.retailClFlag2))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeMarketPostTransparencyInformationFullDepthMessage × List UInt8) := do
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
  let (retailClFlag, bytes) ← decodeUIntLE 1 bytes
  let (secondaryOrderId2, bytes) ← decodeUIntLE 4 bytes
  let (entryDate2, bytes) ← decodeUIntLE 4 bytes
  let (priority2, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 8 bytes
  let (displayQty2, bytes) ← decodeUIntLE 4 bytes
  let (retailClFlag2, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, marketSegmentId, tradingSessionId, trdMatchId, tradeType, lastPx, lastQty, grossTradeAmt, designation, marketMechanism, algoFlag, transactionCategory, strategyTrdMatchId, secondaryOrderId, entryDate, priority, price, displayQty, retailClFlag, secondaryOrderId2, entryDate2, priority2, price2, displayQty2, retailClFlag2 }, bytes)

@[simp] theorem encode_length (message : TradeMarketPostTransparencyInformationFullDepthMessage) : (encode message).length = 104 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeType.encode_length, Designation.encode_length, MarketMechanism.encode_length, TransactionCategory.encode_length]

theorem encode_length_pos (message : TradeMarketPostTransparencyInformationFullDepthMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeMarketPostTransparencyInformationFullDepthMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMarketPostTransparencyInformationFullDepthMessage

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

/-- Rfq Market Pre Transparency Information Message: 189 bytes -/
structure RfqMarketPreTransparencyInformationMessage where
  sequenceNumber : BitVec 32
  rfqid : BitVec 32
  tradingSessionId : BitVec 8
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  midBuyPrice : BitVec 64
  midBuyVolume : BitVec 32
  buyRfQsNumber : BitVec 16
  midSellPrice : BitVec 64
  midSellVolume : BitVec 32
  sellRfQsNumber : BitVec 16
  bidOrders1 : BitVec 16
  bidSize1 : BitVec 32
  bidPx1 : BitVec 64
  askOrders1 : BitVec 16
  askSize1 : BitVec 32
  askPx1 : BitVec 64
  bidOrders2 : BitVec 16
  bidSize2 : BitVec 32
  bidPx2 : BitVec 64
  askOrders2 : BitVec 16
  askSize2 : BitVec 32
  askPx2 : BitVec 64
  bidOrders3 : BitVec 16
  bidSize3 : BitVec 32
  bidPx3 : BitVec 64
  askOrders3 : BitVec 16
  askSize3 : BitVec 32
  askPx3 : BitVec 64
  bidOrders4 : BitVec 16
  bidSize4 : BitVec 32
  bidPx4 : BitVec 64
  askOrders4 : BitVec 16
  askSize4 : BitVec 32
  askPx4 : BitVec 64
  bidOrders5 : BitVec 16
  bidSize5 : BitVec 32
  bidPx5 : BitVec 64
  askOrders5 : BitVec 16
  askSize5 : BitVec 32
  askPx5 : BitVec 64
  deriving DecidableEq, Repr

namespace RfqMarketPreTransparencyInformationMessage

def encode (message : RfqMarketPreTransparencyInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.rfqid
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 8 message.midBuyPrice
    ++ (encodeUIntLE 4 message.midBuyVolume
    ++ (encodeUIntLE 2 message.buyRfQsNumber
    ++ (encodeUIntLE 8 message.midSellPrice
    ++ (encodeUIntLE 4 message.midSellVolume
    ++ (encodeUIntLE 2 message.sellRfQsNumber
    ++ (encodeUIntLE 2 message.bidOrders1
    ++ (encodeUIntLE 4 message.bidSize1
    ++ (encodeUIntLE 8 message.bidPx1
    ++ (encodeUIntLE 2 message.askOrders1
    ++ (encodeUIntLE 4 message.askSize1
    ++ (encodeUIntLE 8 message.askPx1
    ++ (encodeUIntLE 2 message.bidOrders2
    ++ (encodeUIntLE 4 message.bidSize2
    ++ (encodeUIntLE 8 message.bidPx2
    ++ (encodeUIntLE 2 message.askOrders2
    ++ (encodeUIntLE 4 message.askSize2
    ++ (encodeUIntLE 8 message.askPx2
    ++ (encodeUIntLE 2 message.bidOrders3
    ++ (encodeUIntLE 4 message.bidSize3
    ++ (encodeUIntLE 8 message.bidPx3
    ++ (encodeUIntLE 2 message.askOrders3
    ++ (encodeUIntLE 4 message.askSize3
    ++ (encodeUIntLE 8 message.askPx3
    ++ (encodeUIntLE 2 message.bidOrders4
    ++ (encodeUIntLE 4 message.bidSize4
    ++ (encodeUIntLE 8 message.bidPx4
    ++ (encodeUIntLE 2 message.askOrders4
    ++ (encodeUIntLE 4 message.askSize4
    ++ (encodeUIntLE 8 message.askPx4
    ++ (encodeUIntLE 2 message.bidOrders5
    ++ (encodeUIntLE 4 message.bidSize5
    ++ (encodeUIntLE 8 message.bidPx5
    ++ (encodeUIntLE 2 message.askOrders5
    ++ (encodeUIntLE 4 message.askSize5
    ++ (encodeUIntLE 8 message.askPx5))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (RfqMarketPreTransparencyInformationMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (rfqid, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (midBuyPrice, bytes) ← decodeUIntLE 8 bytes
  let (midBuyVolume, bytes) ← decodeUIntLE 4 bytes
  let (buyRfQsNumber, bytes) ← decodeUIntLE 2 bytes
  let (midSellPrice, bytes) ← decodeUIntLE 8 bytes
  let (midSellVolume, bytes) ← decodeUIntLE 4 bytes
  let (sellRfQsNumber, bytes) ← decodeUIntLE 2 bytes
  let (bidOrders1, bytes) ← decodeUIntLE 2 bytes
  let (bidSize1, bytes) ← decodeUIntLE 4 bytes
  let (bidPx1, bytes) ← decodeUIntLE 8 bytes
  let (askOrders1, bytes) ← decodeUIntLE 2 bytes
  let (askSize1, bytes) ← decodeUIntLE 4 bytes
  let (askPx1, bytes) ← decodeUIntLE 8 bytes
  let (bidOrders2, bytes) ← decodeUIntLE 2 bytes
  let (bidSize2, bytes) ← decodeUIntLE 4 bytes
  let (bidPx2, bytes) ← decodeUIntLE 8 bytes
  let (askOrders2, bytes) ← decodeUIntLE 2 bytes
  let (askSize2, bytes) ← decodeUIntLE 4 bytes
  let (askPx2, bytes) ← decodeUIntLE 8 bytes
  let (bidOrders3, bytes) ← decodeUIntLE 2 bytes
  let (bidSize3, bytes) ← decodeUIntLE 4 bytes
  let (bidPx3, bytes) ← decodeUIntLE 8 bytes
  let (askOrders3, bytes) ← decodeUIntLE 2 bytes
  let (askSize3, bytes) ← decodeUIntLE 4 bytes
  let (askPx3, bytes) ← decodeUIntLE 8 bytes
  let (bidOrders4, bytes) ← decodeUIntLE 2 bytes
  let (bidSize4, bytes) ← decodeUIntLE 4 bytes
  let (bidPx4, bytes) ← decodeUIntLE 8 bytes
  let (askOrders4, bytes) ← decodeUIntLE 2 bytes
  let (askSize4, bytes) ← decodeUIntLE 4 bytes
  let (askPx4, bytes) ← decodeUIntLE 8 bytes
  let (bidOrders5, bytes) ← decodeUIntLE 2 bytes
  let (bidSize5, bytes) ← decodeUIntLE 4 bytes
  let (bidPx5, bytes) ← decodeUIntLE 8 bytes
  let (askOrders5, bytes) ← decodeUIntLE 2 bytes
  let (askSize5, bytes) ← decodeUIntLE 4 bytes
  let (askPx5, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequenceNumber, rfqid, tradingSessionId, securityCode, transactionDateAndTime, midBuyPrice, midBuyVolume, buyRfQsNumber, midSellPrice, midSellVolume, sellRfQsNumber, bidOrders1, bidSize1, bidPx1, askOrders1, askSize1, askPx1, bidOrders2, bidSize2, bidPx2, askOrders2, askSize2, askPx2, bidOrders3, bidSize3, bidPx3, askOrders3, askSize3, askPx3, bidOrders4, bidSize4, bidPx4, askOrders4, askSize4, askPx4, bidOrders5, bidSize5, bidPx5, askOrders5, askSize5, askPx5 }, bytes)

@[simp] theorem encode_length (message : RfqMarketPreTransparencyInformationMessage) : (encode message).length = 189 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RfqMarketPreTransparencyInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : RfqMarketPreTransparencyInformationMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RfqMarketPreTransparencyInformationMessage

/-- Topofbook Message: 46 bytes -/
structure TopofbookMessage where
  sequenceNumber : BitVec 32
  securityCode : BitVec 32
  transactionDateAndTime : BitVec 64
  bidOrders1 : BitVec 16
  bidSize1 : BitVec 32
  bidPx1 : BitVec 64
  retailClBidFlag1 : BitVec 8
  askOrders1 : BitVec 16
  askSize1 : BitVec 32
  askPx1 : BitVec 64
  retailClAskFlag1 : BitVec 8
  deriving DecidableEq, Repr

namespace TopofbookMessage

def encode (message : TopofbookMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.transactionDateAndTime
    ++ (encodeUIntLE 2 message.bidOrders1
    ++ (encodeUIntLE 4 message.bidSize1
    ++ (encodeUIntLE 8 message.bidPx1
    ++ (encodeUIntLE 1 message.retailClBidFlag1
    ++ (encodeUIntLE 2 message.askOrders1
    ++ (encodeUIntLE 4 message.askSize1
    ++ (encodeUIntLE 8 message.askPx1
    ++ (encodeUIntLE 1 message.retailClAskFlag1))))))))))

def decode (bytes : List UInt8) : Option (TopofbookMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (transactionDateAndTime, bytes) ← decodeUIntLE 8 bytes
  let (bidOrders1, bytes) ← decodeUIntLE 2 bytes
  let (bidSize1, bytes) ← decodeUIntLE 4 bytes
  let (bidPx1, bytes) ← decodeUIntLE 8 bytes
  let (retailClBidFlag1, bytes) ← decodeUIntLE 1 bytes
  let (askOrders1, bytes) ← decodeUIntLE 2 bytes
  let (askSize1, bytes) ← decodeUIntLE 4 bytes
  let (askPx1, bytes) ← decodeUIntLE 8 bytes
  let (retailClAskFlag1, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, securityCode, transactionDateAndTime, bidOrders1, bidSize1, bidPx1, retailClBidFlag1, askOrders1, askSize1, askPx1, retailClAskFlag1 }, bytes)

@[simp] theorem encode_length (message : TopofbookMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TopofbookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopofbookMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TopofbookMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | logonResponseMessage (message : LogonResponseMessage) -- 8
  | logoutResponseMessage (message : LogoutResponseMessage) -- 11
  | heartbeatMessage (message : HeartbeatMessage) -- 48
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
  | orderBookClearMessage (message : OrderBookClearMessage) -- 129
  | orderMarketPreTransparencyInformationMessage (message : OrderMarketPreTransparencyInformationMessage) -- 3
  | quoteMarketPreTransparencyInformationMessage (message : QuoteMarketPreTransparencyInformationMessage) -- 7
  | orderCancellationMarketMemberMessage (message : OrderCancellationMarketMemberMessage) -- 1
  | quoteCancellationMarketMemberMessage (message : QuoteCancellationMarketMemberMessage) -- 5
  | tradeMarketPostTransparencyInformationTopofbookMessage (message : TradeMarketPostTransparencyInformationTopofbookMessage) -- 16
  | tradeTradeAmendmentOrCancellationMessage (message : TradeTradeAmendmentOrCancellationMessage) -- 24
  | tradeMarketPostTransparencyInformationFullDepthMessage (message : TradeMarketPostTransparencyInformationFullDepthMessage) -- 17
  | indicationOfInterestMessage (message : IndicationOfInterestMessage) -- 54
  | rfqMarketPreTransparencyInformationMessage (message : RfqMarketPreTransparencyInformationMessage) -- 133
  | topofbookMessage (message : TopofbookMessage) -- 130
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .logonResponseMessage _ => 8
  | .logoutResponseMessage _ => 11
  | .heartbeatMessage _ => 48
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
  | .orderBookClearMessage _ => 129
  | .orderMarketPreTransparencyInformationMessage _ => 3
  | .quoteMarketPreTransparencyInformationMessage _ => 7
  | .orderCancellationMarketMemberMessage _ => 1
  | .quoteCancellationMarketMemberMessage _ => 5
  | .tradeMarketPostTransparencyInformationTopofbookMessage _ => 16
  | .tradeTradeAmendmentOrCancellationMessage _ => 24
  | .tradeMarketPostTransparencyInformationFullDepthMessage _ => 17
  | .indicationOfInterestMessage _ => 54
  | .rfqMarketPreTransparencyInformationMessage _ => 133
  | .topofbookMessage _ => 130

def encode : Payload → List UInt8
  | .logonResponseMessage message => LogonResponseMessage.encode message
  | .logoutResponseMessage message => LogoutResponseMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
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
  | .orderBookClearMessage message => OrderBookClearMessage.encode message
  | .orderMarketPreTransparencyInformationMessage message => OrderMarketPreTransparencyInformationMessage.encode message
  | .quoteMarketPreTransparencyInformationMessage message => QuoteMarketPreTransparencyInformationMessage.encode message
  | .orderCancellationMarketMemberMessage message => OrderCancellationMarketMemberMessage.encode message
  | .quoteCancellationMarketMemberMessage message => QuoteCancellationMarketMemberMessage.encode message
  | .tradeMarketPostTransparencyInformationTopofbookMessage message => TradeMarketPostTransparencyInformationTopofbookMessage.encode message
  | .tradeTradeAmendmentOrCancellationMessage message => TradeTradeAmendmentOrCancellationMessage.encode message
  | .tradeMarketPostTransparencyInformationFullDepthMessage message => TradeMarketPostTransparencyInformationFullDepthMessage.encode message
  | .indicationOfInterestMessage message => IndicationOfInterestMessage.encode message
  | .rfqMarketPreTransparencyInformationMessage message => RfqMarketPreTransparencyInformationMessage.encode message
  | .topofbookMessage message => TopofbookMessage.encode message

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
  | orderBookClearMessage inner =>
    simp only [encode, OrderBookClearMessage.encode_length]
    omega
  | orderMarketPreTransparencyInformationMessage inner =>
    simp only [encode, OrderMarketPreTransparencyInformationMessage.encode_length]
    omega
  | quoteMarketPreTransparencyInformationMessage inner =>
    simp only [encode, QuoteMarketPreTransparencyInformationMessage.encode_length]
    omega
  | orderCancellationMarketMemberMessage inner =>
    simp only [encode, OrderCancellationMarketMemberMessage.encode_length]
    omega
  | quoteCancellationMarketMemberMessage inner =>
    simp only [encode, QuoteCancellationMarketMemberMessage.encode_length]
    omega
  | tradeMarketPostTransparencyInformationTopofbookMessage inner =>
    simp only [encode, TradeMarketPostTransparencyInformationTopofbookMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellationMessage inner =>
    simp only [encode, TradeTradeAmendmentOrCancellationMessage.encode_length]
    omega
  | tradeMarketPostTransparencyInformationFullDepthMessage inner =>
    simp only [encode, TradeMarketPostTransparencyInformationFullDepthMessage.encode_length]
    omega
  | indicationOfInterestMessage inner =>
    simp only [encode, IndicationOfInterestMessage.encode_length]
    omega
  | rfqMarketPreTransparencyInformationMessage inner =>
    simp only [encode, RfqMarketPreTransparencyInformationMessage.encode_length]
    omega
  | topofbookMessage inner =>
    simp only [encode, TopofbookMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 8 then (LogonResponseMessage.decode bytes).map fun (message, rest) => (.logonResponseMessage message, rest)
  else if tag = 11 then (LogoutResponseMessage.decode bytes).map fun (message, rest) => (.logoutResponseMessage message, rest)
  else if tag = 48 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
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
  else if tag = 129 then (OrderBookClearMessage.decode bytes).map fun (message, rest) => (.orderBookClearMessage message, rest)
  else if tag = 3 then (OrderMarketPreTransparencyInformationMessage.decode bytes).map fun (message, rest) => (.orderMarketPreTransparencyInformationMessage message, rest)
  else if tag = 7 then (QuoteMarketPreTransparencyInformationMessage.decode bytes).map fun (message, rest) => (.quoteMarketPreTransparencyInformationMessage message, rest)
  else if tag = 1 then (OrderCancellationMarketMemberMessage.decode bytes).map fun (message, rest) => (.orderCancellationMarketMemberMessage message, rest)
  else if tag = 5 then (QuoteCancellationMarketMemberMessage.decode bytes).map fun (message, rest) => (.quoteCancellationMarketMemberMessage message, rest)
  else if tag = 16 then (TradeMarketPostTransparencyInformationTopofbookMessage.decode bytes).map fun (message, rest) => (.tradeMarketPostTransparencyInformationTopofbookMessage message, rest)
  else if tag = 24 then (TradeTradeAmendmentOrCancellationMessage.decode bytes).map fun (message, rest) => (.tradeTradeAmendmentOrCancellationMessage message, rest)
  else if tag = 17 then (TradeMarketPostTransparencyInformationFullDepthMessage.decode bytes).map fun (message, rest) => (.tradeMarketPostTransparencyInformationFullDepthMessage message, rest)
  else if tag = 54 then (IndicationOfInterestMessage.decode bytes).map fun (message, rest) => (.indicationOfInterestMessage message, rest)
  else if tag = 133 then (RfqMarketPreTransparencyInformationMessage.decode bytes).map fun (message, rest) => (.rfqMarketPreTransparencyInformationMessage message, rest)
  else if tag = 130 then (TopofbookMessage.decode bytes).map fun (message, rest) => (.topofbookMessage message, rest)
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
  | orderBookClearMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookClearMessage.encode_length]
    omega
  | orderMarketPreTransparencyInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderMarketPreTransparencyInformationMessage.encode_length]
    omega
  | quoteMarketPreTransparencyInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteMarketPreTransparencyInformationMessage.encode_length]
    omega
  | orderCancellationMarketMemberMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancellationMarketMemberMessage.encode_length]
    omega
  | quoteCancellationMarketMemberMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteCancellationMarketMemberMessage.encode_length]
    omega
  | tradeMarketPostTransparencyInformationTopofbookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMarketPostTransparencyInformationTopofbookMessage.encode_length]
    omega
  | tradeTradeAmendmentOrCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeTradeAmendmentOrCancellationMessage.encode_length]
    omega
  | tradeMarketPostTransparencyInformationFullDepthMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMarketPostTransparencyInformationFullDepthMessage.encode_length]
    omega
  | indicationOfInterestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndicationOfInterestMessage.encode_length]
    omega
  | rfqMarketPreTransparencyInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RfqMarketPreTransparencyInformationMessage.encode_length]
    omega
  | topofbookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TopofbookMessage.encode_length]
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

end Omi.BmeMeffRecoveryBmegateV16
