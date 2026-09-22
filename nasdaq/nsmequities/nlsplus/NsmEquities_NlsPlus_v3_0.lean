import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Last Sale Plus v3.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesNlsplusItchV30

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4D, 0x45, 0x43]

inductive EventCode where
  | startOfTransmissions -- Start Of Transmissions
  | startOfSystemHours -- Start Of System Hours
  | startOfMarketHours -- Start Of Market Hours
  | endOfMarketHours -- End Of Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfTransmissions -- End Of Transmissions
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfTransmissions => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfMarketHours => 0x51
  | .endOfMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfTransmissions => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfTransmissions
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x45 then .endOfSystemHours
  else .endOfTransmissions

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfTransmissions => decide
  | startOfSystemHours => decide
  | startOfMarketHours => decide
  | endOfMarketHours => decide
  | endOfSystemHours => decide
  | endOfTransmissions => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Originating Market Center Identifier: one byte code -/
def OriginatingMarketCenterIdentifier.codes : List UInt8 :=
  [0x51, 0x4C, 0x32, 0x42, 0x58]

inductive OriginatingMarketCenterIdentifier where
  | nasdaq -- Nasdaq
  | trfCarteret -- Trf Carteret
  | trfChicago -- Trf Chicago
  | bx -- Bx
  | psx -- Psx
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginatingMarketCenterIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginatingMarketCenterIdentifier

def toByte : OriginatingMarketCenterIdentifier → UInt8
  | .nasdaq => 0x51
  | .trfCarteret => 0x4C
  | .trfChicago => 0x32
  | .bx => 0x42
  | .psx => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginatingMarketCenterIdentifier :=
  if byte = 0x51 then .nasdaq
  else if byte = 0x4C then .trfCarteret
  else if byte = 0x32 then .trfChicago
  else if byte = 0x42 then .bx
  else .psx

def ofByte (byte : UInt8) : OriginatingMarketCenterIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginatingMarketCenterIdentifier) : ofByte value.toByte = value := by
  cases value with
  | nasdaq => decide
  | trfCarteret => decide
  | trfChicago => decide
  | bx => decide
  | psx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginatingMarketCenterIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginatingMarketCenterIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginatingMarketCenterIdentifier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginatingMarketCenterIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginatingMarketCenterIdentifier

/-- Security Class: one byte code -/
def SecurityClass.codes : List UInt8 :=
  [0x51, 0x4E, 0x41, 0x50, 0x4D, 0x5A, 0x56]

inductive SecurityClass where
  | nasdaq -- Nasdaq
  | nyse -- Nyse
  | nyseAmerican -- Nyse American
  | nyseArca -- Nyse Arca
  | nyseTexas -- Nyse Texas
  | bats -- Bats
  | iex -- Iex
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityClass.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityClass

def toByte : SecurityClass → UInt8
  | .nasdaq => 0x51
  | .nyse => 0x4E
  | .nyseAmerican => 0x41
  | .nyseArca => 0x50
  | .nyseTexas => 0x4D
  | .bats => 0x5A
  | .iex => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityClass :=
  if byte = 0x51 then .nasdaq
  else if byte = 0x4E then .nyse
  else if byte = 0x41 then .nyseAmerican
  else if byte = 0x50 then .nyseArca
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x5A then .bats
  else .iex

def ofByte (byte : UInt8) : SecurityClass :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityClass) : ofByte value.toByte = value := by
  cases value with
  | nasdaq => decide
  | nyse => decide
  | nyseAmerican => decide
  | nyseArca => decide
  | nyseTexas => decide
  | bats => decide
  | iex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityClass) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityClass × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityClass) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityClass) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityClass

/-- Settlement Type: one byte code -/
def SettlementType.codes : List UInt8 :=
  [0x40, 0x43, 0x4E, 0x52]

inductive SettlementType where
  | regularSettlement -- Regular Settlement
  | cashSettlement -- Cash Settlement
  | nextDaySettlement -- Next Day Settlement
  | sellerSettlement -- Seller Settlement
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementType

def toByte : SettlementType → UInt8
  | .regularSettlement => 0x40
  | .cashSettlement => 0x43
  | .nextDaySettlement => 0x4E
  | .sellerSettlement => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementType :=
  if byte = 0x40 then .regularSettlement
  else if byte = 0x43 then .cashSettlement
  else if byte = 0x4E then .nextDaySettlement
  else .sellerSettlement

def ofByte (byte : UInt8) : SettlementType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementType) : ofByte value.toByte = value := by
  cases value with
  | regularSettlement => decide
  | cashSettlement => decide
  | nextDaySettlement => decide
  | sellerSettlement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlementType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementType

/-- Trade Through Exemption: one byte code -/
def TradeThroughExemption.codes : List UInt8 :=
  [0x46, 0x4F, 0x34, 0x35, 0x36, 0x37, 0x20]

inductive TradeThroughExemption where
  | intermarketSweep -- Intermarket Sweep
  | openingPrint -- Opening Print
  | derivativePriced -- Derivative Priced
  | reOpeningPrint -- Re Opening Print
  | closingPrint -- Closing Print
  | qualifiedContingentTrade -- Qualified Contingent Trade
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeThroughExemption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeThroughExemption

def toByte : TradeThroughExemption → UInt8
  | .intermarketSweep => 0x46
  | .openingPrint => 0x4F
  | .derivativePriced => 0x34
  | .reOpeningPrint => 0x35
  | .closingPrint => 0x36
  | .qualifiedContingentTrade => 0x37
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeThroughExemption :=
  if byte = 0x46 then .intermarketSweep
  else if byte = 0x4F then .openingPrint
  else if byte = 0x34 then .derivativePriced
  else if byte = 0x35 then .reOpeningPrint
  else if byte = 0x36 then .closingPrint
  else if byte = 0x37 then .qualifiedContingentTrade
  else .notApplicable

def ofByte (byte : UInt8) : TradeThroughExemption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeThroughExemption) : ofByte value.toByte = value := by
  cases value with
  | intermarketSweep => decide
  | openingPrint => decide
  | derivativePriced => decide
  | reOpeningPrint => decide
  | closingPrint => decide
  | qualifiedContingentTrade => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeThroughExemption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeThroughExemption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeThroughExemption) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeThroughExemption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeThroughExemption

/-- Extended Hours Or Sold Code: one byte code -/
def ExtendedHoursOrSoldCode.codes : List UInt8 :=
  [0x54, 0x55, 0x4C, 0x5A, 0x20]

inductive ExtendedHoursOrSoldCode where
  | extendedHoursTrade -- Extended Hours Trade
  | extendedHoursTradeReportedLate -- Extended Hours Trade Reported Late
  | soldLast -- Sold Last
  | soldOutOfSequence -- Sold Out Of Sequence
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ ExtendedHoursOrSoldCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExtendedHoursOrSoldCode

def toByte : ExtendedHoursOrSoldCode → UInt8
  | .extendedHoursTrade => 0x54
  | .extendedHoursTradeReportedLate => 0x55
  | .soldLast => 0x4C
  | .soldOutOfSequence => 0x5A
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExtendedHoursOrSoldCode :=
  if byte = 0x54 then .extendedHoursTrade
  else if byte = 0x55 then .extendedHoursTradeReportedLate
  else if byte = 0x4C then .soldLast
  else if byte = 0x5A then .soldOutOfSequence
  else .notApplicable

def ofByte (byte : UInt8) : ExtendedHoursOrSoldCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExtendedHoursOrSoldCode) : ofByte value.toByte = value := by
  cases value with
  | extendedHoursTrade => decide
  | extendedHoursTradeReportedLate => decide
  | soldLast => decide
  | soldOutOfSequence => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExtendedHoursOrSoldCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExtendedHoursOrSoldCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExtendedHoursOrSoldCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExtendedHoursOrSoldCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExtendedHoursOrSoldCode

/-- Special Sale Condition: one byte code -/
def SpecialSaleCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x44, 0x48, 0x4D, 0x50, 0x51, 0x53, 0x56, 0x57, 0x58, 0x6F, 0x78, 0x20]

inductive SpecialSaleCondition where
  | acquisition -- Acquisition
  | bunched -- Bunched
  | distribution -- Distribution
  | priceVariationTransaction -- Price Variation Transaction
  | nasdaqOfficialClosePrice -- Nasdaq Official Close Price
  | priorReferencePrice -- Prior Reference Price
  | nasdaqOfficialOpeningPrice -- Nasdaq Official Opening Price
  | splitTrade -- Split Trade
  | contingentTrade -- Contingent Trade
  | averagePriceTrade -- Average Price Trade
  | crossTrade -- Cross Trade
  | oddLotExecution -- Odd Lot Execution
  | oddLotCrossExecution -- Odd Lot Cross Execution
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ SpecialSaleCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SpecialSaleCondition

def toByte : SpecialSaleCondition → UInt8
  | .acquisition => 0x41
  | .bunched => 0x42
  | .distribution => 0x44
  | .priceVariationTransaction => 0x48
  | .nasdaqOfficialClosePrice => 0x4D
  | .priorReferencePrice => 0x50
  | .nasdaqOfficialOpeningPrice => 0x51
  | .splitTrade => 0x53
  | .contingentTrade => 0x56
  | .averagePriceTrade => 0x57
  | .crossTrade => 0x58
  | .oddLotExecution => 0x6F
  | .oddLotCrossExecution => 0x78
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SpecialSaleCondition :=
  if byte = 0x41 then .acquisition
  else if byte = 0x42 then .bunched
  else if byte = 0x44 then .distribution
  else if byte = 0x48 then .priceVariationTransaction
  else if byte = 0x4D then .nasdaqOfficialClosePrice
  else if byte = 0x50 then .priorReferencePrice
  else if byte = 0x51 then .nasdaqOfficialOpeningPrice
  else if byte = 0x53 then .splitTrade
  else if byte = 0x56 then .contingentTrade
  else if byte = 0x57 then .averagePriceTrade
  else if byte = 0x58 then .crossTrade
  else if byte = 0x6F then .oddLotExecution
  else if byte = 0x78 then .oddLotCrossExecution
  else .notApplicable

def ofByte (byte : UInt8) : SpecialSaleCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SpecialSaleCondition) : ofByte value.toByte = value := by
  cases value with
  | acquisition => decide
  | bunched => decide
  | distribution => decide
  | priceVariationTransaction => decide
  | nasdaqOfficialClosePrice => decide
  | priorReferencePrice => decide
  | nasdaqOfficialOpeningPrice => decide
  | splitTrade => decide
  | contingentTrade => decide
  | averagePriceTrade => decide
  | crossTrade => decide
  | oddLotExecution => decide
  | oddLotCrossExecution => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SpecialSaleCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SpecialSaleCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SpecialSaleCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SpecialSaleCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SpecialSaleCondition

/-- Original Settlement Type: one byte code -/
def OriginalSettlementType.codes : List UInt8 :=
  [0x40, 0x43, 0x4E, 0x52]

inductive OriginalSettlementType where
  | regularSettlement -- Regular Settlement
  | cashSettlement -- Cash Settlement
  | nextDaySettlement -- Next Day Settlement
  | sellerSettlement -- Seller Settlement
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalSettlementType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalSettlementType

def toByte : OriginalSettlementType → UInt8
  | .regularSettlement => 0x40
  | .cashSettlement => 0x43
  | .nextDaySettlement => 0x4E
  | .sellerSettlement => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalSettlementType :=
  if byte = 0x40 then .regularSettlement
  else if byte = 0x43 then .cashSettlement
  else if byte = 0x4E then .nextDaySettlement
  else .sellerSettlement

def ofByte (byte : UInt8) : OriginalSettlementType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalSettlementType) : ofByte value.toByte = value := by
  cases value with
  | regularSettlement => decide
  | cashSettlement => decide
  | nextDaySettlement => decide
  | sellerSettlement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalSettlementType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalSettlementType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalSettlementType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginalSettlementType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalSettlementType

/-- Original Trade Through Exemption: one byte code -/
def OriginalTradeThroughExemption.codes : List UInt8 :=
  [0x46, 0x4F, 0x34, 0x35, 0x36, 0x37, 0x20]

inductive OriginalTradeThroughExemption where
  | intermarketSweep -- Intermarket Sweep
  | openingPrint -- Opening Print
  | derivativePriced -- Derivative Priced
  | reOpeningPrint -- Re Opening Print
  | closingPrint -- Closing Print
  | qualifiedContingentTrade -- Qualified Contingent Trade
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalTradeThroughExemption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalTradeThroughExemption

def toByte : OriginalTradeThroughExemption → UInt8
  | .intermarketSweep => 0x46
  | .openingPrint => 0x4F
  | .derivativePriced => 0x34
  | .reOpeningPrint => 0x35
  | .closingPrint => 0x36
  | .qualifiedContingentTrade => 0x37
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalTradeThroughExemption :=
  if byte = 0x46 then .intermarketSweep
  else if byte = 0x4F then .openingPrint
  else if byte = 0x34 then .derivativePriced
  else if byte = 0x35 then .reOpeningPrint
  else if byte = 0x36 then .closingPrint
  else if byte = 0x37 then .qualifiedContingentTrade
  else .notApplicable

def ofByte (byte : UInt8) : OriginalTradeThroughExemption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalTradeThroughExemption) : ofByte value.toByte = value := by
  cases value with
  | intermarketSweep => decide
  | openingPrint => decide
  | derivativePriced => decide
  | reOpeningPrint => decide
  | closingPrint => decide
  | qualifiedContingentTrade => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalTradeThroughExemption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalTradeThroughExemption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalTradeThroughExemption) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginalTradeThroughExemption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalTradeThroughExemption

/-- Original Extended Hours Or Sold Code: one byte code -/
def OriginalExtendedHoursOrSoldCode.codes : List UInt8 :=
  [0x54, 0x55, 0x4C, 0x5A, 0x20]

inductive OriginalExtendedHoursOrSoldCode where
  | extendedHoursTrade -- Extended Hours Trade
  | extendedHoursTradeReportedLate -- Extended Hours Trade Reported Late
  | soldLast -- Sold Last
  | soldOutOfSequence -- Sold Out Of Sequence
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalExtendedHoursOrSoldCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalExtendedHoursOrSoldCode

def toByte : OriginalExtendedHoursOrSoldCode → UInt8
  | .extendedHoursTrade => 0x54
  | .extendedHoursTradeReportedLate => 0x55
  | .soldLast => 0x4C
  | .soldOutOfSequence => 0x5A
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalExtendedHoursOrSoldCode :=
  if byte = 0x54 then .extendedHoursTrade
  else if byte = 0x55 then .extendedHoursTradeReportedLate
  else if byte = 0x4C then .soldLast
  else if byte = 0x5A then .soldOutOfSequence
  else .notApplicable

def ofByte (byte : UInt8) : OriginalExtendedHoursOrSoldCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalExtendedHoursOrSoldCode) : ofByte value.toByte = value := by
  cases value with
  | extendedHoursTrade => decide
  | extendedHoursTradeReportedLate => decide
  | soldLast => decide
  | soldOutOfSequence => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalExtendedHoursOrSoldCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalExtendedHoursOrSoldCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalExtendedHoursOrSoldCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginalExtendedHoursOrSoldCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalExtendedHoursOrSoldCode

/-- Original Special Sale Condition: one byte code -/
def OriginalSpecialSaleCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x44, 0x48, 0x4D, 0x50, 0x51, 0x53, 0x56, 0x57, 0x58, 0x6F, 0x78, 0x20]

inductive OriginalSpecialSaleCondition where
  | acquisition -- Acquisition
  | bunched -- Bunched
  | distribution -- Distribution
  | priceVariationTransaction -- Price Variation Transaction
  | nasdaqOfficialClosePrice -- Nasdaq Official Close Price
  | priorReferencePrice -- Prior Reference Price
  | nasdaqOfficialOpeningPrice -- Nasdaq Official Opening Price
  | splitTrade -- Split Trade
  | contingentTrade -- Contingent Trade
  | averagePriceTrade -- Average Price Trade
  | crossTrade -- Cross Trade
  | oddLotExecution -- Odd Lot Execution
  | oddLotCrossExecution -- Odd Lot Cross Execution
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalSpecialSaleCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalSpecialSaleCondition

def toByte : OriginalSpecialSaleCondition → UInt8
  | .acquisition => 0x41
  | .bunched => 0x42
  | .distribution => 0x44
  | .priceVariationTransaction => 0x48
  | .nasdaqOfficialClosePrice => 0x4D
  | .priorReferencePrice => 0x50
  | .nasdaqOfficialOpeningPrice => 0x51
  | .splitTrade => 0x53
  | .contingentTrade => 0x56
  | .averagePriceTrade => 0x57
  | .crossTrade => 0x58
  | .oddLotExecution => 0x6F
  | .oddLotCrossExecution => 0x78
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalSpecialSaleCondition :=
  if byte = 0x41 then .acquisition
  else if byte = 0x42 then .bunched
  else if byte = 0x44 then .distribution
  else if byte = 0x48 then .priceVariationTransaction
  else if byte = 0x4D then .nasdaqOfficialClosePrice
  else if byte = 0x50 then .priorReferencePrice
  else if byte = 0x51 then .nasdaqOfficialOpeningPrice
  else if byte = 0x53 then .splitTrade
  else if byte = 0x56 then .contingentTrade
  else if byte = 0x57 then .averagePriceTrade
  else if byte = 0x58 then .crossTrade
  else if byte = 0x6F then .oddLotExecution
  else if byte = 0x78 then .oddLotCrossExecution
  else .notApplicable

def ofByte (byte : UInt8) : OriginalSpecialSaleCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalSpecialSaleCondition) : ofByte value.toByte = value := by
  cases value with
  | acquisition => decide
  | bunched => decide
  | distribution => decide
  | priceVariationTransaction => decide
  | nasdaqOfficialClosePrice => decide
  | priorReferencePrice => decide
  | nasdaqOfficialOpeningPrice => decide
  | splitTrade => decide
  | contingentTrade => decide
  | averagePriceTrade => decide
  | crossTrade => decide
  | oddLotExecution => decide
  | oddLotCrossExecution => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalSpecialSaleCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalSpecialSaleCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalSpecialSaleCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginalSpecialSaleCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalSpecialSaleCondition

/-- Market Center: one byte code -/
def MarketCenter.codes : List UInt8 :=
  [0x51, 0x4C, 0x32]

inductive MarketCenter where
  | nasdaq -- Nasdaq
  | trfCarteret -- Trf Carteret
  | trfChicago -- Trf Chicago
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCenter.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCenter

def toByte : MarketCenter → UInt8
  | .nasdaq => 0x51
  | .trfCarteret => 0x4C
  | .trfChicago => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCenter :=
  if byte = 0x51 then .nasdaq
  else if byte = 0x4C then .trfCarteret
  else .trfChicago

def ofByte (byte : UInt8) : MarketCenter :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCenter) : ofByte value.toByte = value := by
  cases value with
  | nasdaq => decide
  | trfCarteret => decide
  | trfChicago => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCenter) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCenter × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCenter) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCenter) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCenter

/-- Corrected Settlement Type: one byte code -/
def CorrectedSettlementType.codes : List UInt8 :=
  [0x40, 0x43, 0x4E, 0x52]

inductive CorrectedSettlementType where
  | regularSettlement -- Regular Settlement
  | cashSettlement -- Cash Settlement
  | nextDaySettlement -- Next Day Settlement
  | sellerSettlement -- Seller Settlement
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedSettlementType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedSettlementType

def toByte : CorrectedSettlementType → UInt8
  | .regularSettlement => 0x40
  | .cashSettlement => 0x43
  | .nextDaySettlement => 0x4E
  | .sellerSettlement => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedSettlementType :=
  if byte = 0x40 then .regularSettlement
  else if byte = 0x43 then .cashSettlement
  else if byte = 0x4E then .nextDaySettlement
  else .sellerSettlement

def ofByte (byte : UInt8) : CorrectedSettlementType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedSettlementType) : ofByte value.toByte = value := by
  cases value with
  | regularSettlement => decide
  | cashSettlement => decide
  | nextDaySettlement => decide
  | sellerSettlement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedSettlementType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedSettlementType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedSettlementType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CorrectedSettlementType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedSettlementType

/-- Corrected Trade Through Exemption: one byte code -/
def CorrectedTradeThroughExemption.codes : List UInt8 :=
  [0x46, 0x4F, 0x34, 0x35, 0x36, 0x37, 0x20]

inductive CorrectedTradeThroughExemption where
  | intermarketSweep -- Intermarket Sweep
  | openingPrint -- Opening Print
  | derivativePriced -- Derivative Priced
  | reOpeningPrint -- Re Opening Print
  | closingPrint -- Closing Print
  | qualifiedContingentTrade -- Qualified Contingent Trade
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedTradeThroughExemption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedTradeThroughExemption

def toByte : CorrectedTradeThroughExemption → UInt8
  | .intermarketSweep => 0x46
  | .openingPrint => 0x4F
  | .derivativePriced => 0x34
  | .reOpeningPrint => 0x35
  | .closingPrint => 0x36
  | .qualifiedContingentTrade => 0x37
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedTradeThroughExemption :=
  if byte = 0x46 then .intermarketSweep
  else if byte = 0x4F then .openingPrint
  else if byte = 0x34 then .derivativePriced
  else if byte = 0x35 then .reOpeningPrint
  else if byte = 0x36 then .closingPrint
  else if byte = 0x37 then .qualifiedContingentTrade
  else .notApplicable

def ofByte (byte : UInt8) : CorrectedTradeThroughExemption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedTradeThroughExemption) : ofByte value.toByte = value := by
  cases value with
  | intermarketSweep => decide
  | openingPrint => decide
  | derivativePriced => decide
  | reOpeningPrint => decide
  | closingPrint => decide
  | qualifiedContingentTrade => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedTradeThroughExemption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedTradeThroughExemption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedTradeThroughExemption) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CorrectedTradeThroughExemption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedTradeThroughExemption

/-- Corrected Extended Hours Or Sold Code: one byte code -/
def CorrectedExtendedHoursOrSoldCode.codes : List UInt8 :=
  [0x54, 0x55, 0x4C, 0x5A, 0x20]

inductive CorrectedExtendedHoursOrSoldCode where
  | extendedHoursTrade -- Extended Hours Trade
  | extendedHoursTradeReportedLate -- Extended Hours Trade Reported Late
  | soldLast -- Sold Last
  | soldOutOfSequence -- Sold Out Of Sequence
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedExtendedHoursOrSoldCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedExtendedHoursOrSoldCode

def toByte : CorrectedExtendedHoursOrSoldCode → UInt8
  | .extendedHoursTrade => 0x54
  | .extendedHoursTradeReportedLate => 0x55
  | .soldLast => 0x4C
  | .soldOutOfSequence => 0x5A
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedExtendedHoursOrSoldCode :=
  if byte = 0x54 then .extendedHoursTrade
  else if byte = 0x55 then .extendedHoursTradeReportedLate
  else if byte = 0x4C then .soldLast
  else if byte = 0x5A then .soldOutOfSequence
  else .notApplicable

def ofByte (byte : UInt8) : CorrectedExtendedHoursOrSoldCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedExtendedHoursOrSoldCode) : ofByte value.toByte = value := by
  cases value with
  | extendedHoursTrade => decide
  | extendedHoursTradeReportedLate => decide
  | soldLast => decide
  | soldOutOfSequence => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedExtendedHoursOrSoldCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedExtendedHoursOrSoldCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedExtendedHoursOrSoldCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CorrectedExtendedHoursOrSoldCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedExtendedHoursOrSoldCode

/-- Corrected Special Sale Condition: one byte code -/
def CorrectedSpecialSaleCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x44, 0x48, 0x4D, 0x50, 0x51, 0x53, 0x56, 0x57, 0x58, 0x6F, 0x78, 0x20]

inductive CorrectedSpecialSaleCondition where
  | acquisition -- Acquisition
  | bunched -- Bunched
  | distribution -- Distribution
  | priceVariationTransaction -- Price Variation Transaction
  | nasdaqOfficialClosePrice -- Nasdaq Official Close Price
  | priorReferencePrice -- Prior Reference Price
  | nasdaqOfficialOpeningPrice -- Nasdaq Official Opening Price
  | splitTrade -- Split Trade
  | contingentTrade -- Contingent Trade
  | averagePriceTrade -- Average Price Trade
  | crossTrade -- Cross Trade
  | oddLotExecution -- Odd Lot Execution
  | oddLotCrossExecution -- Odd Lot Cross Execution
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedSpecialSaleCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedSpecialSaleCondition

def toByte : CorrectedSpecialSaleCondition → UInt8
  | .acquisition => 0x41
  | .bunched => 0x42
  | .distribution => 0x44
  | .priceVariationTransaction => 0x48
  | .nasdaqOfficialClosePrice => 0x4D
  | .priorReferencePrice => 0x50
  | .nasdaqOfficialOpeningPrice => 0x51
  | .splitTrade => 0x53
  | .contingentTrade => 0x56
  | .averagePriceTrade => 0x57
  | .crossTrade => 0x58
  | .oddLotExecution => 0x6F
  | .oddLotCrossExecution => 0x78
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedSpecialSaleCondition :=
  if byte = 0x41 then .acquisition
  else if byte = 0x42 then .bunched
  else if byte = 0x44 then .distribution
  else if byte = 0x48 then .priceVariationTransaction
  else if byte = 0x4D then .nasdaqOfficialClosePrice
  else if byte = 0x50 then .priorReferencePrice
  else if byte = 0x51 then .nasdaqOfficialOpeningPrice
  else if byte = 0x53 then .splitTrade
  else if byte = 0x56 then .contingentTrade
  else if byte = 0x57 then .averagePriceTrade
  else if byte = 0x58 then .crossTrade
  else if byte = 0x6F then .oddLotExecution
  else if byte = 0x78 then .oddLotCrossExecution
  else .notApplicable

def ofByte (byte : UInt8) : CorrectedSpecialSaleCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedSpecialSaleCondition) : ofByte value.toByte = value := by
  cases value with
  | acquisition => decide
  | bunched => decide
  | distribution => decide
  | priceVariationTransaction => decide
  | nasdaqOfficialClosePrice => decide
  | priorReferencePrice => decide
  | nasdaqOfficialOpeningPrice => decide
  | splitTrade => decide
  | contingentTrade => decide
  | averagePriceTrade => decide
  | crossTrade => decide
  | oddLotExecution => decide
  | oddLotCrossExecution => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedSpecialSaleCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedSpecialSaleCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedSpecialSaleCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CorrectedSpecialSaleCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedSpecialSaleCondition

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x48, 0x50, 0x51, 0x54]

inductive CurrentTradingState where
  | halted -- Halted
  | paused -- Paused
  | quotationOnly -- Quotation Only
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .halted => 0x48
  | .paused => 0x50
  | .quotationOnly => 0x51
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .halted
  else if byte = 0x50 then .paused
  else if byte = 0x51 then .quotationOnly
  else .trading

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | paused => decide
  | quotationOnly => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CurrentTradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CurrentTradingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CurrentTradingState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CurrentTradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CurrentTradingState

/-- Market Category: one byte code -/
def MarketCategory.codes : List UInt8 :=
  [0x51, 0x47, 0x53, 0x4E, 0x41, 0x50, 0x4D, 0x5A, 0x56]

inductive MarketCategory where
  | nasdaqGlobalSelectMarket -- Nasdaq Global Select Market
  | nasdaqGlobalMarket -- Nasdaq Global Market
  | nasdaqCapitalMarket -- Nasdaq Capital Market
  | nyse -- Nyse
  | nyseAmerican -- Nyse American
  | nyseArca -- Nyse Arca
  | nyseTexas -- Nyse Texas
  | bats -- Bats
  | iex -- Iex
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCategory

def toByte : MarketCategory → UInt8
  | .nasdaqGlobalSelectMarket => 0x51
  | .nasdaqGlobalMarket => 0x47
  | .nasdaqCapitalMarket => 0x53
  | .nyse => 0x4E
  | .nyseAmerican => 0x41
  | .nyseArca => 0x50
  | .nyseTexas => 0x4D
  | .bats => 0x5A
  | .iex => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCategory :=
  if byte = 0x51 then .nasdaqGlobalSelectMarket
  else if byte = 0x47 then .nasdaqGlobalMarket
  else if byte = 0x53 then .nasdaqCapitalMarket
  else if byte = 0x4E then .nyse
  else if byte = 0x41 then .nyseAmerican
  else if byte = 0x50 then .nyseArca
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x5A then .bats
  else .iex

def ofByte (byte : UInt8) : MarketCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCategory) : ofByte value.toByte = value := by
  cases value with
  | nasdaqGlobalSelectMarket => decide
  | nasdaqGlobalMarket => decide
  | nasdaqCapitalMarket => decide
  | nyse => decide
  | nyseAmerican => decide
  | nyseArca => decide
  | nyseTexas => decide
  | bats => decide
  | iex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCategory

/-- Financial Status Indicator: one byte code -/
def FinancialStatusIndicator.codes : List UInt8 :=
  [0x44, 0x45, 0x51, 0x53, 0x47, 0x48, 0x4A, 0x4B, 0x43, 0x4E, 0x20]

inductive FinancialStatusIndicator where
  | deficient -- Deficient
  | delinquent -- Delinquent
  | bankrupt -- Bankrupt
  | suspended -- Suspended
  | deficientAndBankrupt -- Deficient And Bankrupt
  | deficientAndDelinquent -- Deficient And Delinquent
  | delinquentAndBankrupt -- Delinquent And Bankrupt
  | deficientDelinquentAndBankrupt -- Deficient Delinquent And Bankrupt
  | creationsOrRedemptionsSuspended -- Creations Or Redemptions Suspended
  | normal -- Normal
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ FinancialStatusIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinancialStatusIndicator

def toByte : FinancialStatusIndicator → UInt8
  | .deficient => 0x44
  | .delinquent => 0x45
  | .bankrupt => 0x51
  | .suspended => 0x53
  | .deficientAndBankrupt => 0x47
  | .deficientAndDelinquent => 0x48
  | .delinquentAndBankrupt => 0x4A
  | .deficientDelinquentAndBankrupt => 0x4B
  | .creationsOrRedemptionsSuspended => 0x43
  | .normal => 0x4E
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinancialStatusIndicator :=
  if byte = 0x44 then .deficient
  else if byte = 0x45 then .delinquent
  else if byte = 0x51 then .bankrupt
  else if byte = 0x53 then .suspended
  else if byte = 0x47 then .deficientAndBankrupt
  else if byte = 0x48 then .deficientAndDelinquent
  else if byte = 0x4A then .delinquentAndBankrupt
  else if byte = 0x4B then .deficientDelinquentAndBankrupt
  else if byte = 0x43 then .creationsOrRedemptionsSuspended
  else if byte = 0x4E then .normal
  else .notAvailable

def ofByte (byte : UInt8) : FinancialStatusIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinancialStatusIndicator) : ofByte value.toByte = value := by
  cases value with
  | deficient => decide
  | delinquent => decide
  | bankrupt => decide
  | suspended => decide
  | deficientAndBankrupt => decide
  | deficientAndDelinquent => decide
  | delinquentAndBankrupt => decide
  | deficientDelinquentAndBankrupt => decide
  | creationsOrRedemptionsSuspended => decide
  | normal => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FinancialStatusIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinancialStatusIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FinancialStatusIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FinancialStatusIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FinancialStatusIndicator

/-- Round Lots Only: one byte code -/
def RoundLotsOnly.codes : List UInt8 :=
  [0x59, 0x4E]

inductive RoundLotsOnly where
  | roundLotsOnly -- Round Lots Only
  | noRestriction -- No Restriction
  | unlisted (byte : { byte : UInt8 // byte ∉ RoundLotsOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RoundLotsOnly

def toByte : RoundLotsOnly → UInt8
  | .roundLotsOnly => 0x59
  | .noRestriction => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RoundLotsOnly :=
  if byte = 0x59 then .roundLotsOnly
  else .noRestriction

def ofByte (byte : UInt8) : RoundLotsOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RoundLotsOnly) : ofByte value.toByte = value := by
  cases value with
  | roundLotsOnly => decide
  | noRestriction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RoundLotsOnly) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RoundLotsOnly × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RoundLotsOnly) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RoundLotsOnly) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RoundLotsOnly

/-- Issue Classification: one byte code -/
def IssueClassification.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x46, 0x49, 0x4C, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57]

inductive IssueClassification where
  | americanDepositaryShare -- American Depositary Share
  | bond -- Bond
  | commonStock -- Common Stock
  | depositoryReceipt -- Depository Receipt
  | rule144A -- Rule 144 A
  | limitedPartnership -- Limited Partnership
  | notes -- Notes
  | ordinaryShare -- Ordinary Share
  | preferredStock -- Preferred Stock
  | otherSecurities -- Other Securities
  | right -- Right
  | sharesOfBeneficialInterest -- Shares Of Beneficial Interest
  | convertibleDebenture -- Convertible Debenture
  | unit -- Unit
  | unitsOfBeneficialInterest -- Units Of Beneficial Interest
  | warrant -- Warrant
  | unlisted (byte : { byte : UInt8 // byte ∉ IssueClassification.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IssueClassification

def toByte : IssueClassification → UInt8
  | .americanDepositaryShare => 0x41
  | .bond => 0x42
  | .commonStock => 0x43
  | .depositoryReceipt => 0x46
  | .rule144A => 0x49
  | .limitedPartnership => 0x4C
  | .notes => 0x4E
  | .ordinaryShare => 0x4F
  | .preferredStock => 0x50
  | .otherSecurities => 0x51
  | .right => 0x52
  | .sharesOfBeneficialInterest => 0x53
  | .convertibleDebenture => 0x54
  | .unit => 0x55
  | .unitsOfBeneficialInterest => 0x56
  | .warrant => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IssueClassification :=
  if byte = 0x41 then .americanDepositaryShare
  else if byte = 0x42 then .bond
  else if byte = 0x43 then .commonStock
  else if byte = 0x46 then .depositoryReceipt
  else if byte = 0x49 then .rule144A
  else if byte = 0x4C then .limitedPartnership
  else if byte = 0x4E then .notes
  else if byte = 0x4F then .ordinaryShare
  else if byte = 0x50 then .preferredStock
  else if byte = 0x51 then .otherSecurities
  else if byte = 0x52 then .right
  else if byte = 0x53 then .sharesOfBeneficialInterest
  else if byte = 0x54 then .convertibleDebenture
  else if byte = 0x55 then .unit
  else if byte = 0x56 then .unitsOfBeneficialInterest
  else .warrant

def ofByte (byte : UInt8) : IssueClassification :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IssueClassification) : ofByte value.toByte = value := by
  cases value with
  | americanDepositaryShare => decide
  | bond => decide
  | commonStock => decide
  | depositoryReceipt => decide
  | rule144A => decide
  | limitedPartnership => decide
  | notes => decide
  | ordinaryShare => decide
  | preferredStock => decide
  | otherSecurities => decide
  | right => decide
  | sharesOfBeneficialInterest => decide
  | convertibleDebenture => decide
  | unit => decide
  | unitsOfBeneficialInterest => decide
  | warrant => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IssueClassification) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IssueClassification × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IssueClassification) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IssueClassification) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IssueClassification

/-- Authenticity: one byte code -/
def Authenticity.codes : List UInt8 :=
  [0x50, 0x54]

inductive Authenticity where
  | production -- Production
  | test -- Test
  | unlisted (byte : { byte : UInt8 // byte ∉ Authenticity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Authenticity

def toByte : Authenticity → UInt8
  | .production => 0x50
  | .test => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Authenticity :=
  if byte = 0x50 then .production
  else .test

def ofByte (byte : UInt8) : Authenticity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Authenticity) : ofByte value.toByte = value := by
  cases value with
  | production => decide
  | test => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Authenticity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Authenticity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Authenticity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Authenticity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Authenticity

/-- Short Sale Threshold Indicator: one byte code -/
def ShortSaleThresholdIndicator.codes : List UInt8 :=
  [0x59, 0x4E, 0x20]

inductive ShortSaleThresholdIndicator where
  | restricted -- Restricted
  | notRestricted -- Not Restricted
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSaleThresholdIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSaleThresholdIndicator

def toByte : ShortSaleThresholdIndicator → UInt8
  | .restricted => 0x59
  | .notRestricted => 0x4E
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSaleThresholdIndicator :=
  if byte = 0x59 then .restricted
  else if byte = 0x4E then .notRestricted
  else .notAvailable

def ofByte (byte : UInt8) : ShortSaleThresholdIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSaleThresholdIndicator) : ofByte value.toByte = value := by
  cases value with
  | restricted => decide
  | notRestricted => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSaleThresholdIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSaleThresholdIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSaleThresholdIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ShortSaleThresholdIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSaleThresholdIndicator

/-- Ipo Flag: one byte code -/
def IpoFlag.codes : List UInt8 :=
  [0x59, 0x4E, 0x20]

inductive IpoFlag where
  | newIpo -- New Ipo
  | notNewIpo -- Not New Ipo
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ IpoFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IpoFlag

def toByte : IpoFlag → UInt8
  | .newIpo => 0x59
  | .notNewIpo => 0x4E
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IpoFlag :=
  if byte = 0x59 then .newIpo
  else if byte = 0x4E then .notNewIpo
  else .notAvailable

def ofByte (byte : UInt8) : IpoFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IpoFlag) : ofByte value.toByte = value := by
  cases value with
  | newIpo => decide
  | notNewIpo => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IpoFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IpoFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IpoFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IpoFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IpoFlag

/-- Luld Reference Price Tier: one byte code -/
def LuldReferencePriceTier.codes : List UInt8 :=
  [0x31, 0x32, 0x20]

inductive LuldReferencePriceTier where
  | tier1 -- Tier 1
  | tier2 -- Tier 2
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ LuldReferencePriceTier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LuldReferencePriceTier

def toByte : LuldReferencePriceTier → UInt8
  | .tier1 => 0x31
  | .tier2 => 0x32
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LuldReferencePriceTier :=
  if byte = 0x31 then .tier1
  else if byte = 0x32 then .tier2
  else .notApplicable

def ofByte (byte : UInt8) : LuldReferencePriceTier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LuldReferencePriceTier) : ofByte value.toByte = value := by
  cases value with
  | tier1 => decide
  | tier2 => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LuldReferencePriceTier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LuldReferencePriceTier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LuldReferencePriceTier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LuldReferencePriceTier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LuldReferencePriceTier

/-- Etp Flag: one byte code -/
def EtpFlag.codes : List UInt8 :=
  [0x59, 0x4E, 0x20]

inductive EtpFlag where
  | etp -- Etp
  | notEtp -- Not Etp
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ EtpFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EtpFlag

def toByte : EtpFlag → UInt8
  | .etp => 0x59
  | .notEtp => 0x4E
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EtpFlag :=
  if byte = 0x59 then .etp
  else if byte = 0x4E then .notEtp
  else .notAvailable

def ofByte (byte : UInt8) : EtpFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EtpFlag) : ofByte value.toByte = value := by
  cases value with
  | etp => decide
  | notEtp => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EtpFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EtpFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EtpFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EtpFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EtpFlag

/-- Inverse Indicator: one byte code -/
def InverseIndicator.codes : List UInt8 :=
  [0x59, 0x4E]

inductive InverseIndicator where
  | inverse -- Inverse
  | notInverse -- Not Inverse
  | unlisted (byte : { byte : UInt8 // byte ∉ InverseIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InverseIndicator

def toByte : InverseIndicator → UInt8
  | .inverse => 0x59
  | .notInverse => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InverseIndicator :=
  if byte = 0x59 then .inverse
  else .notInverse

def ofByte (byte : UInt8) : InverseIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InverseIndicator) : ofByte value.toByte = value := by
  cases value with
  | inverse => decide
  | notInverse => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InverseIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InverseIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InverseIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InverseIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InverseIndicator

/-- Reg Sho Action: one byte code -/
def RegShoAction.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive RegShoAction where
  | noPriceTest -- No Price Test
  | restrictionInEffect -- Restriction In Effect
  | restrictionRemains -- Restriction Remains
  | unlisted (byte : { byte : UInt8 // byte ∉ RegShoAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RegShoAction

def toByte : RegShoAction → UInt8
  | .noPriceTest => 0x30
  | .restrictionInEffect => 0x31
  | .restrictionRemains => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RegShoAction :=
  if byte = 0x30 then .noPriceTest
  else if byte = 0x31 then .restrictionInEffect
  else .restrictionRemains

def ofByte (byte : UInt8) : RegShoAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RegShoAction) : ofByte value.toByte = value := by
  cases value with
  | noPriceTest => decide
  | restrictionInEffect => decide
  | restrictionRemains => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RegShoAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RegShoAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RegShoAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RegShoAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RegShoAction

/-- Reference For Net Change: one byte code -/
def ReferenceForNetChange.codes : List UInt8 :=
  [0x46, 0x57]

inductive ReferenceForNetChange where
  | firstTradePrice -- First Trade Price
  | underwriterPrice -- Underwriter Price
  | unlisted (byte : { byte : UInt8 // byte ∉ ReferenceForNetChange.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReferenceForNetChange

def toByte : ReferenceForNetChange → UInt8
  | .firstTradePrice => 0x46
  | .underwriterPrice => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReferenceForNetChange :=
  if byte = 0x46 then .firstTradePrice
  else .underwriterPrice

def ofByte (byte : UInt8) : ReferenceForNetChange :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReferenceForNetChange) : ofByte value.toByte = value := by
  cases value with
  | firstTradePrice => decide
  | underwriterPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReferenceForNetChange) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReferenceForNetChange × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReferenceForNetChange) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReferenceForNetChange) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReferenceForNetChange

/-- Breached Level: one byte code -/
def BreachedLevel.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive BreachedLevel where
  | level1 -- Level 1
  | level2 -- Level 2
  | level3 -- Level 3
  | unlisted (byte : { byte : UInt8 // byte ∉ BreachedLevel.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BreachedLevel

def toByte : BreachedLevel → UInt8
  | .level1 => 0x31
  | .level2 => 0x32
  | .level3 => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BreachedLevel :=
  if byte = 0x31 then .level1
  else if byte = 0x32 then .level2
  else .level3

def ofByte (byte : UInt8) : BreachedLevel :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BreachedLevel) : ofByte value.toByte = value := by
  cases value with
  | level1 => decide
  | level2 => decide
  | level3 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BreachedLevel) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BreachedLevel × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BreachedLevel) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BreachedLevel) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BreachedLevel

/-- Ipo Quotation Release Qualifier: one byte code -/
def IpoQuotationReleaseQualifier.codes : List UInt8 :=
  [0x41, 0x43]

inductive IpoQuotationReleaseQualifier where
  | anticipated -- Anticipated
  | cancelled -- Cancelled
  | unlisted (byte : { byte : UInt8 // byte ∉ IpoQuotationReleaseQualifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IpoQuotationReleaseQualifier

def toByte : IpoQuotationReleaseQualifier → UInt8
  | .anticipated => 0x41
  | .cancelled => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IpoQuotationReleaseQualifier :=
  if byte = 0x41 then .anticipated
  else .cancelled

def ofByte (byte : UInt8) : IpoQuotationReleaseQualifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IpoQuotationReleaseQualifier) : ofByte value.toByte = value := by
  cases value with
  | anticipated => decide
  | cancelled => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IpoQuotationReleaseQualifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IpoQuotationReleaseQualifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IpoQuotationReleaseQualifier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IpoQuotationReleaseQualifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IpoQuotationReleaseQualifier

/-- Market Code: one byte code -/
def MarketCode.codes : List UInt8 :=
  [0x51, 0x42, 0x58]

inductive MarketCode where
  | nasdaq -- Nasdaq
  | bx -- Bx
  | psx -- Psx
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCode

def toByte : MarketCode → UInt8
  | .nasdaq => 0x51
  | .bx => 0x42
  | .psx => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCode :=
  if byte = 0x51 then .nasdaq
  else if byte = 0x42 then .bx
  else .psx

def ofByte (byte : UInt8) : MarketCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCode) : ofByte value.toByte = value := by
  cases value with
  | nasdaq => decide
  | bx => decide
  | psx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCode

/-- Operational Halt Action: one byte code -/
def OperationalHaltAction.codes : List UInt8 :=
  [0x48, 0x54]

inductive OperationalHaltAction where
  | halted -- Halted
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ OperationalHaltAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OperationalHaltAction

def toByte : OperationalHaltAction → UInt8
  | .halted => 0x48
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OperationalHaltAction :=
  if byte = 0x48 then .halted
  else .trading

def ofByte (byte : UInt8) : OperationalHaltAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OperationalHaltAction) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OperationalHaltAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OperationalHaltAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OperationalHaltAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OperationalHaltAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OperationalHaltAction

/-- System Event Message: 1 bytes -/
structure SystemEventMessage where
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  EventCode.encode message.eventCode

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Sale Condition Modifier: 4 bytes -/
structure SaleConditionModifier where
  settlementType : SettlementType
  tradeThroughExemption : TradeThroughExemption
  extendedHoursOrSoldCode : ExtendedHoursOrSoldCode
  specialSaleCondition : SpecialSaleCondition
  deriving DecidableEq, Repr

namespace SaleConditionModifier

def encode (message : SaleConditionModifier) : List UInt8 :=
  SettlementType.encode message.settlementType
    ++ (TradeThroughExemption.encode message.tradeThroughExemption
    ++ (ExtendedHoursOrSoldCode.encode message.extendedHoursOrSoldCode
    ++ (SpecialSaleCondition.encode message.specialSaleCondition)))

def decode (bytes : List UInt8) : Option (SaleConditionModifier × List UInt8) := do
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (tradeThroughExemption, bytes) ← TradeThroughExemption.decode bytes
  let (extendedHoursOrSoldCode, bytes) ← ExtendedHoursOrSoldCode.decode bytes
  let (specialSaleCondition, bytes) ← SpecialSaleCondition.decode bytes
  pure ({ settlementType, tradeThroughExemption, extendedHoursOrSoldCode, specialSaleCondition }, bytes)

@[simp] theorem encode_length (message : SaleConditionModifier) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, SettlementType.encode_length, TradeThroughExemption.encode_length, ExtendedHoursOrSoldCode.encode_length, SpecialSaleCondition.encode_length]

theorem encode_length_pos (message : SaleConditionModifier) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SaleConditionModifier) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExtendedHoursOrSoldCode.decode_encode, some_bind]
  dsimp only
  rw [SpecialSaleCondition.decode_encode, some_bind]
  rfl

end SaleConditionModifier

/-- Trade Report Message: 40 bytes -/
structure TradeReportMessage where
  originatingMarketCenterIdentifier : OriginatingMarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  tradeControlNumber : Alpha 10
  tradePrice : BitVec 32
  tradeSize : BitVec 32
  saleConditionModifier : SaleConditionModifier
  consolidatedVolume : BitVec 64
  deriving DecidableEq, Repr

namespace TradeReportMessage

def encode (message : TradeReportMessage) : List UInt8 :=
  OriginatingMarketCenterIdentifier.encode message.originatingMarketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.tradeControlNumber
    ++ (encodeUInt 4 message.tradePrice
    ++ (encodeUInt 4 message.tradeSize
    ++ (SaleConditionModifier.encode message.saleConditionModifier
    ++ (encodeUInt 8 message.consolidatedVolume)))))))

def decode (bytes : List UInt8) : Option (TradeReportMessage × List UInt8) := do
  let (originatingMarketCenterIdentifier, bytes) ← OriginatingMarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (tradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (tradeSize, bytes) ← decodeUInt 4 bytes
  let (saleConditionModifier, bytes) ← SaleConditionModifier.decode bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  pure ({ originatingMarketCenterIdentifier, issueSymbol, securityClass, tradeControlNumber, tradePrice, tradeSize, saleConditionModifier, consolidatedVolume }, bytes)

@[simp] theorem encode_length (message : TradeReportMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, OriginatingMarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length, SaleConditionModifier.encode_length]

theorem encode_length_pos (message : TradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OriginatingMarketCenterIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeReportMessage

/-- Long Form Trade Report Message: 44 bytes -/
structure LongFormTradeReportMessage where
  originatingMarketCenterIdentifier : OriginatingMarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  tradeControlNumber : Alpha 10
  tradePriceLong : BitVec 64
  tradeSize : BitVec 32
  saleConditionModifier : SaleConditionModifier
  consolidatedVolume : BitVec 64
  deriving DecidableEq, Repr

namespace LongFormTradeReportMessage

def encode (message : LongFormTradeReportMessage) : List UInt8 :=
  OriginatingMarketCenterIdentifier.encode message.originatingMarketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.tradeControlNumber
    ++ (encodeUInt 8 message.tradePriceLong
    ++ (encodeUInt 4 message.tradeSize
    ++ (SaleConditionModifier.encode message.saleConditionModifier
    ++ (encodeUInt 8 message.consolidatedVolume)))))))

def decode (bytes : List UInt8) : Option (LongFormTradeReportMessage × List UInt8) := do
  let (originatingMarketCenterIdentifier, bytes) ← OriginatingMarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (tradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (tradePriceLong, bytes) ← decodeUInt 8 bytes
  let (tradeSize, bytes) ← decodeUInt 4 bytes
  let (saleConditionModifier, bytes) ← SaleConditionModifier.decode bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  pure ({ originatingMarketCenterIdentifier, issueSymbol, securityClass, tradeControlNumber, tradePriceLong, tradeSize, saleConditionModifier, consolidatedVolume }, bytes)

@[simp] theorem encode_length (message : LongFormTradeReportMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, OriginatingMarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length, SaleConditionModifier.encode_length]

theorem encode_length_pos (message : LongFormTradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongFormTradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OriginatingMarketCenterIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LongFormTradeReportMessage

/-- Next Shares Trade Report Message: 44 bytes -/
structure NextSharesTradeReportMessage where
  originatingMarketCenterIdentifier : OriginatingMarketCenterIdentifier
  nextSharesSymbol : Alpha 8
  securityClass : SecurityClass
  tradeControlNumber : Alpha 10
  proxyPrice : BitVec 32
  tradeSize : BitVec 32
  navOffsetAmount : BitVec 32
  saleConditionModifier : SaleConditionModifier
  consolidatedVolume : BitVec 64
  deriving DecidableEq, Repr

namespace NextSharesTradeReportMessage

def encode (message : NextSharesTradeReportMessage) : List UInt8 :=
  OriginatingMarketCenterIdentifier.encode message.originatingMarketCenterIdentifier
    ++ (Alpha.encode message.nextSharesSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.tradeControlNumber
    ++ (encodeUInt 4 message.proxyPrice
    ++ (encodeUInt 4 message.tradeSize
    ++ (encodeUInt 4 message.navOffsetAmount
    ++ (SaleConditionModifier.encode message.saleConditionModifier
    ++ (encodeUInt 8 message.consolidatedVolume))))))))

def decode (bytes : List UInt8) : Option (NextSharesTradeReportMessage × List UInt8) := do
  let (originatingMarketCenterIdentifier, bytes) ← OriginatingMarketCenterIdentifier.decode bytes
  let (nextSharesSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (tradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (proxyPrice, bytes) ← decodeUInt 4 bytes
  let (tradeSize, bytes) ← decodeUInt 4 bytes
  let (navOffsetAmount, bytes) ← decodeUInt 4 bytes
  let (saleConditionModifier, bytes) ← SaleConditionModifier.decode bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  pure ({ originatingMarketCenterIdentifier, nextSharesSymbol, securityClass, tradeControlNumber, proxyPrice, tradeSize, navOffsetAmount, saleConditionModifier, consolidatedVolume }, bytes)

@[simp] theorem encode_length (message : NextSharesTradeReportMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, OriginatingMarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length, SaleConditionModifier.encode_length]

theorem encode_length_pos (message : NextSharesTradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NextSharesTradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OriginatingMarketCenterIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NextSharesTradeReportMessage

/-- Original Sale Condition Modifier: 4 bytes -/
structure OriginalSaleConditionModifier where
  originalSettlementType : OriginalSettlementType
  originalTradeThroughExemption : OriginalTradeThroughExemption
  originalExtendedHoursOrSoldCode : OriginalExtendedHoursOrSoldCode
  originalSpecialSaleCondition : OriginalSpecialSaleCondition
  deriving DecidableEq, Repr

namespace OriginalSaleConditionModifier

def encode (message : OriginalSaleConditionModifier) : List UInt8 :=
  OriginalSettlementType.encode message.originalSettlementType
    ++ (OriginalTradeThroughExemption.encode message.originalTradeThroughExemption
    ++ (OriginalExtendedHoursOrSoldCode.encode message.originalExtendedHoursOrSoldCode
    ++ (OriginalSpecialSaleCondition.encode message.originalSpecialSaleCondition)))

def decode (bytes : List UInt8) : Option (OriginalSaleConditionModifier × List UInt8) := do
  let (originalSettlementType, bytes) ← OriginalSettlementType.decode bytes
  let (originalTradeThroughExemption, bytes) ← OriginalTradeThroughExemption.decode bytes
  let (originalExtendedHoursOrSoldCode, bytes) ← OriginalExtendedHoursOrSoldCode.decode bytes
  let (originalSpecialSaleCondition, bytes) ← OriginalSpecialSaleCondition.decode bytes
  pure ({ originalSettlementType, originalTradeThroughExemption, originalExtendedHoursOrSoldCode, originalSpecialSaleCondition }, bytes)

@[simp] theorem encode_length (message : OriginalSaleConditionModifier) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, OriginalSettlementType.encode_length, OriginalTradeThroughExemption.encode_length, OriginalExtendedHoursOrSoldCode.encode_length, OriginalSpecialSaleCondition.encode_length]

theorem encode_length_pos (message : OriginalSaleConditionModifier) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OriginalSaleConditionModifier) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OriginalSettlementType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalTradeThroughExemption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalExtendedHoursOrSoldCode.decode_encode, some_bind]
  dsimp only
  rw [OriginalSpecialSaleCondition.decode_encode, some_bind]
  rfl

end OriginalSaleConditionModifier

/-- Trade Cancel Error Message: 40 bytes -/
structure TradeCancelErrorMessage where
  originatingMarketCenterIdentifier : OriginatingMarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  originalTradeControlNumber : Alpha 10
  originalTradePrice : BitVec 32
  originalTradeSize : BitVec 32
  originalSaleConditionModifier : OriginalSaleConditionModifier
  consolidatedVolume : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCancelErrorMessage

def encode (message : TradeCancelErrorMessage) : List UInt8 :=
  OriginatingMarketCenterIdentifier.encode message.originatingMarketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.originalTradeControlNumber
    ++ (encodeUInt 4 message.originalTradePrice
    ++ (encodeUInt 4 message.originalTradeSize
    ++ (OriginalSaleConditionModifier.encode message.originalSaleConditionModifier
    ++ (encodeUInt 8 message.consolidatedVolume)))))))

def decode (bytes : List UInt8) : Option (TradeCancelErrorMessage × List UInt8) := do
  let (originatingMarketCenterIdentifier, bytes) ← OriginatingMarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (originalTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (originalTradePrice, bytes) ← decodeUInt 4 bytes
  let (originalTradeSize, bytes) ← decodeUInt 4 bytes
  let (originalSaleConditionModifier, bytes) ← OriginalSaleConditionModifier.decode bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  pure ({ originatingMarketCenterIdentifier, issueSymbol, securityClass, originalTradeControlNumber, originalTradePrice, originalTradeSize, originalSaleConditionModifier, consolidatedVolume }, bytes)

@[simp] theorem encode_length (message : TradeCancelErrorMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, OriginatingMarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length, OriginalSaleConditionModifier.encode_length]

theorem encode_length_pos (message : TradeCancelErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OriginatingMarketCenterIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCancelErrorMessage

/-- Long Form Trade Cancel Error Message: 44 bytes -/
structure LongFormTradeCancelErrorMessage where
  originatingMarketCenterIdentifier : OriginatingMarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  originalTradeControlNumber : Alpha 10
  originalTradePriceLong : BitVec 64
  originalTradeSize : BitVec 32
  originalSaleConditionModifier : OriginalSaleConditionModifier
  consolidatedVolume : BitVec 64
  deriving DecidableEq, Repr

namespace LongFormTradeCancelErrorMessage

def encode (message : LongFormTradeCancelErrorMessage) : List UInt8 :=
  OriginatingMarketCenterIdentifier.encode message.originatingMarketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.originalTradeControlNumber
    ++ (encodeUInt 8 message.originalTradePriceLong
    ++ (encodeUInt 4 message.originalTradeSize
    ++ (OriginalSaleConditionModifier.encode message.originalSaleConditionModifier
    ++ (encodeUInt 8 message.consolidatedVolume)))))))

def decode (bytes : List UInt8) : Option (LongFormTradeCancelErrorMessage × List UInt8) := do
  let (originatingMarketCenterIdentifier, bytes) ← OriginatingMarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (originalTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (originalTradePriceLong, bytes) ← decodeUInt 8 bytes
  let (originalTradeSize, bytes) ← decodeUInt 4 bytes
  let (originalSaleConditionModifier, bytes) ← OriginalSaleConditionModifier.decode bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  pure ({ originatingMarketCenterIdentifier, issueSymbol, securityClass, originalTradeControlNumber, originalTradePriceLong, originalTradeSize, originalSaleConditionModifier, consolidatedVolume }, bytes)

@[simp] theorem encode_length (message : LongFormTradeCancelErrorMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, OriginatingMarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length, OriginalSaleConditionModifier.encode_length]

theorem encode_length_pos (message : LongFormTradeCancelErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongFormTradeCancelErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OriginatingMarketCenterIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LongFormTradeCancelErrorMessage

/-- Next Shares Trade Cancel Error Message: 44 bytes -/
structure NextSharesTradeCancelErrorMessage where
  marketCenter : MarketCenter
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  originalTradeControlNumber : Alpha 10
  originalProxyPrice : BitVec 32
  originalNavOffsetAmount : BitVec 32
  originalTradeSize : BitVec 32
  originalSaleConditionModifier : OriginalSaleConditionModifier
  consolidatedVolume : BitVec 64
  deriving DecidableEq, Repr

namespace NextSharesTradeCancelErrorMessage

def encode (message : NextSharesTradeCancelErrorMessage) : List UInt8 :=
  MarketCenter.encode message.marketCenter
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.originalTradeControlNumber
    ++ (encodeUInt 4 message.originalProxyPrice
    ++ (encodeUInt 4 message.originalNavOffsetAmount
    ++ (encodeUInt 4 message.originalTradeSize
    ++ (OriginalSaleConditionModifier.encode message.originalSaleConditionModifier
    ++ (encodeUInt 8 message.consolidatedVolume))))))))

def decode (bytes : List UInt8) : Option (NextSharesTradeCancelErrorMessage × List UInt8) := do
  let (marketCenter, bytes) ← MarketCenter.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (originalTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (originalProxyPrice, bytes) ← decodeUInt 4 bytes
  let (originalNavOffsetAmount, bytes) ← decodeUInt 4 bytes
  let (originalTradeSize, bytes) ← decodeUInt 4 bytes
  let (originalSaleConditionModifier, bytes) ← OriginalSaleConditionModifier.decode bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  pure ({ marketCenter, issueSymbol, securityClass, originalTradeControlNumber, originalProxyPrice, originalNavOffsetAmount, originalTradeSize, originalSaleConditionModifier, consolidatedVolume }, bytes)

@[simp] theorem encode_length (message : NextSharesTradeCancelErrorMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, MarketCenter.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length, OriginalSaleConditionModifier.encode_length]

theorem encode_length_pos (message : NextSharesTradeCancelErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NextSharesTradeCancelErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketCenter.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NextSharesTradeCancelErrorMessage

/-- Corrected Sale Condition Modifier: 4 bytes -/
structure CorrectedSaleConditionModifier where
  correctedSettlementType : CorrectedSettlementType
  correctedTradeThroughExemption : CorrectedTradeThroughExemption
  correctedExtendedHoursOrSoldCode : CorrectedExtendedHoursOrSoldCode
  correctedSpecialSaleCondition : CorrectedSpecialSaleCondition
  deriving DecidableEq, Repr

namespace CorrectedSaleConditionModifier

def encode (message : CorrectedSaleConditionModifier) : List UInt8 :=
  CorrectedSettlementType.encode message.correctedSettlementType
    ++ (CorrectedTradeThroughExemption.encode message.correctedTradeThroughExemption
    ++ (CorrectedExtendedHoursOrSoldCode.encode message.correctedExtendedHoursOrSoldCode
    ++ (CorrectedSpecialSaleCondition.encode message.correctedSpecialSaleCondition)))

def decode (bytes : List UInt8) : Option (CorrectedSaleConditionModifier × List UInt8) := do
  let (correctedSettlementType, bytes) ← CorrectedSettlementType.decode bytes
  let (correctedTradeThroughExemption, bytes) ← CorrectedTradeThroughExemption.decode bytes
  let (correctedExtendedHoursOrSoldCode, bytes) ← CorrectedExtendedHoursOrSoldCode.decode bytes
  let (correctedSpecialSaleCondition, bytes) ← CorrectedSpecialSaleCondition.decode bytes
  pure ({ correctedSettlementType, correctedTradeThroughExemption, correctedExtendedHoursOrSoldCode, correctedSpecialSaleCondition }, bytes)

@[simp] theorem encode_length (message : CorrectedSaleConditionModifier) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, CorrectedSettlementType.encode_length, CorrectedTradeThroughExemption.encode_length, CorrectedExtendedHoursOrSoldCode.encode_length, CorrectedSpecialSaleCondition.encode_length]

theorem encode_length_pos (message : CorrectedSaleConditionModifier) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CorrectedSaleConditionModifier) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, CorrectedSettlementType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedTradeThroughExemption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedExtendedHoursOrSoldCode.decode_encode, some_bind]
  dsimp only
  rw [CorrectedSpecialSaleCondition.decode_encode, some_bind]
  rfl

end CorrectedSaleConditionModifier

/-- Trade Correction Message: 62 bytes -/
structure TradeCorrectionMessage where
  originatingMarketCenterIdentifier : OriginatingMarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  originalTradeControlNumber : Alpha 10
  originalTradePrice : BitVec 32
  originalTradeSize : BitVec 32
  originalSaleConditionModifier : OriginalSaleConditionModifier
  correctedTradeControlNumber : Alpha 10
  correctedTradePrice : BitVec 32
  correctedTradeSize : BitVec 32
  correctedSaleConditionModifier : CorrectedSaleConditionModifier
  consolidatedVolume : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  OriginatingMarketCenterIdentifier.encode message.originatingMarketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.originalTradeControlNumber
    ++ (encodeUInt 4 message.originalTradePrice
    ++ (encodeUInt 4 message.originalTradeSize
    ++ (OriginalSaleConditionModifier.encode message.originalSaleConditionModifier
    ++ (Alpha.encode message.correctedTradeControlNumber
    ++ (encodeUInt 4 message.correctedTradePrice
    ++ (encodeUInt 4 message.correctedTradeSize
    ++ (CorrectedSaleConditionModifier.encode message.correctedSaleConditionModifier
    ++ (encodeUInt 8 message.consolidatedVolume)))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (originatingMarketCenterIdentifier, bytes) ← OriginatingMarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (originalTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (originalTradePrice, bytes) ← decodeUInt 4 bytes
  let (originalTradeSize, bytes) ← decodeUInt 4 bytes
  let (originalSaleConditionModifier, bytes) ← OriginalSaleConditionModifier.decode bytes
  let (correctedTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (correctedTradePrice, bytes) ← decodeUInt 4 bytes
  let (correctedTradeSize, bytes) ← decodeUInt 4 bytes
  let (correctedSaleConditionModifier, bytes) ← CorrectedSaleConditionModifier.decode bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  pure ({ originatingMarketCenterIdentifier, issueSymbol, securityClass, originalTradeControlNumber, originalTradePrice, originalTradeSize, originalSaleConditionModifier, correctedTradeControlNumber, correctedTradePrice, correctedTradeSize, correctedSaleConditionModifier, consolidatedVolume }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, OriginatingMarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length, OriginalSaleConditionModifier.encode_length, CorrectedSaleConditionModifier.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OriginatingMarketCenterIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedSaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCorrectionMessage

/-- Long Form Trade Correction Message: 70 bytes -/
structure LongFormTradeCorrectionMessage where
  originatingMarketCenterIdentifier : OriginatingMarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  originalTradeControlNumber : Alpha 10
  originalTradePriceLong : BitVec 64
  originalTradeSize : BitVec 32
  originalSaleConditionModifier : OriginalSaleConditionModifier
  correctedTradeControlNumber : Alpha 10
  correctedTradePriceLong : BitVec 64
  correctedTradeSize : BitVec 32
  correctedSaleConditionModifier : CorrectedSaleConditionModifier
  consolidatedVolume : BitVec 64
  deriving DecidableEq, Repr

namespace LongFormTradeCorrectionMessage

def encode (message : LongFormTradeCorrectionMessage) : List UInt8 :=
  OriginatingMarketCenterIdentifier.encode message.originatingMarketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.originalTradeControlNumber
    ++ (encodeUInt 8 message.originalTradePriceLong
    ++ (encodeUInt 4 message.originalTradeSize
    ++ (OriginalSaleConditionModifier.encode message.originalSaleConditionModifier
    ++ (Alpha.encode message.correctedTradeControlNumber
    ++ (encodeUInt 8 message.correctedTradePriceLong
    ++ (encodeUInt 4 message.correctedTradeSize
    ++ (CorrectedSaleConditionModifier.encode message.correctedSaleConditionModifier
    ++ (encodeUInt 8 message.consolidatedVolume)))))))))))

def decode (bytes : List UInt8) : Option (LongFormTradeCorrectionMessage × List UInt8) := do
  let (originatingMarketCenterIdentifier, bytes) ← OriginatingMarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (originalTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (originalTradePriceLong, bytes) ← decodeUInt 8 bytes
  let (originalTradeSize, bytes) ← decodeUInt 4 bytes
  let (originalSaleConditionModifier, bytes) ← OriginalSaleConditionModifier.decode bytes
  let (correctedTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (correctedTradePriceLong, bytes) ← decodeUInt 8 bytes
  let (correctedTradeSize, bytes) ← decodeUInt 4 bytes
  let (correctedSaleConditionModifier, bytes) ← CorrectedSaleConditionModifier.decode bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  pure ({ originatingMarketCenterIdentifier, issueSymbol, securityClass, originalTradeControlNumber, originalTradePriceLong, originalTradeSize, originalSaleConditionModifier, correctedTradeControlNumber, correctedTradePriceLong, correctedTradeSize, correctedSaleConditionModifier, consolidatedVolume }, bytes)

@[simp] theorem encode_length (message : LongFormTradeCorrectionMessage) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, OriginatingMarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length, OriginalSaleConditionModifier.encode_length, CorrectedSaleConditionModifier.encode_length]

theorem encode_length_pos (message : LongFormTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongFormTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OriginatingMarketCenterIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedSaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LongFormTradeCorrectionMessage

/-- Next Shares Trade Correction Message: 70 bytes -/
structure NextSharesTradeCorrectionMessage where
  marketCenter : MarketCenter
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  originalTradeControlNumber : Alpha 10
  originalProxyPrice : BitVec 32
  originalNavOffsetAmount : BitVec 32
  originalTradeSize : BitVec 32
  originalSaleConditionModifier : OriginalSaleConditionModifier
  correctedTradeControlNumber : Alpha 10
  correctedProxyPrice : BitVec 32
  correctedNavOffsetAmount : BitVec 32
  correctedTradeSize : BitVec 32
  correctedSaleConditionModifier : CorrectedSaleConditionModifier
  consolidatedVolume : BitVec 64
  deriving DecidableEq, Repr

namespace NextSharesTradeCorrectionMessage

def encode (message : NextSharesTradeCorrectionMessage) : List UInt8 :=
  MarketCenter.encode message.marketCenter
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.originalTradeControlNumber
    ++ (encodeUInt 4 message.originalProxyPrice
    ++ (encodeUInt 4 message.originalNavOffsetAmount
    ++ (encodeUInt 4 message.originalTradeSize
    ++ (OriginalSaleConditionModifier.encode message.originalSaleConditionModifier
    ++ (Alpha.encode message.correctedTradeControlNumber
    ++ (encodeUInt 4 message.correctedProxyPrice
    ++ (encodeUInt 4 message.correctedNavOffsetAmount
    ++ (encodeUInt 4 message.correctedTradeSize
    ++ (CorrectedSaleConditionModifier.encode message.correctedSaleConditionModifier
    ++ (encodeUInt 8 message.consolidatedVolume)))))))))))))

def decode (bytes : List UInt8) : Option (NextSharesTradeCorrectionMessage × List UInt8) := do
  let (marketCenter, bytes) ← MarketCenter.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (originalTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (originalProxyPrice, bytes) ← decodeUInt 4 bytes
  let (originalNavOffsetAmount, bytes) ← decodeUInt 4 bytes
  let (originalTradeSize, bytes) ← decodeUInt 4 bytes
  let (originalSaleConditionModifier, bytes) ← OriginalSaleConditionModifier.decode bytes
  let (correctedTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (correctedProxyPrice, bytes) ← decodeUInt 4 bytes
  let (correctedNavOffsetAmount, bytes) ← decodeUInt 4 bytes
  let (correctedTradeSize, bytes) ← decodeUInt 4 bytes
  let (correctedSaleConditionModifier, bytes) ← CorrectedSaleConditionModifier.decode bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  pure ({ marketCenter, issueSymbol, securityClass, originalTradeControlNumber, originalProxyPrice, originalNavOffsetAmount, originalTradeSize, originalSaleConditionModifier, correctedTradeControlNumber, correctedProxyPrice, correctedNavOffsetAmount, correctedTradeSize, correctedSaleConditionModifier, consolidatedVolume }, bytes)

@[simp] theorem encode_length (message : NextSharesTradeCorrectionMessage) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, MarketCenter.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length, OriginalSaleConditionModifier.encode_length, CorrectedSaleConditionModifier.encode_length]

theorem encode_length_pos (message : NextSharesTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NextSharesTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketCenter.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedSaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NextSharesTradeCorrectionMessage

/-- Stock Trading Action Message: 15 bytes -/
structure StockTradingActionMessage where
  reserved : Alpha 1
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  currentTradingState : CurrentTradingState
  reason : Alpha 4
  deriving DecidableEq, Repr

namespace StockTradingActionMessage

def encode (message : StockTradingActionMessage) : List UInt8 :=
  Alpha.encode message.reserved
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (CurrentTradingState.encode message.currentTradingState
    ++ (Alpha.encode message.reason))))

def decode (bytes : List UInt8) : Option (StockTradingActionMessage × List UInt8) := do
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  let (reason, bytes) ← Alpha.decode 4 bytes
  pure ({ reserved, issueSymbol, securityClass, currentTradingState, reason }, bytes)

@[simp] theorem encode_length (message : StockTradingActionMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SecurityClass.encode_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : StockTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CurrentTradingState.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockTradingActionMessage

/-- Stock Directory Message: 40 bytes -/
structure StockDirectoryMessage where
  stock : Alpha 8
  marketCategory : MarketCategory
  financialStatusIndicator : FinancialStatusIndicator
  roundLotSize : BitVec 32
  roundLotsOnly : RoundLotsOnly
  issueClassification : IssueClassification
  issueSubType : Alpha 2
  authenticity : Authenticity
  shortSaleThresholdIndicator : ShortSaleThresholdIndicator
  ipoFlag : IpoFlag
  luldReferencePriceTier : LuldReferencePriceTier
  etpFlag : EtpFlag
  etpLeverageFactor : BitVec 32
  inverseIndicator : InverseIndicator
  bloombergId : Alpha 12
  deriving DecidableEq, Repr

namespace StockDirectoryMessage

def encode (message : StockDirectoryMessage) : List UInt8 :=
  Alpha.encode message.stock
    ++ (MarketCategory.encode message.marketCategory
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (encodeUInt 4 message.roundLotSize
    ++ (RoundLotsOnly.encode message.roundLotsOnly
    ++ (IssueClassification.encode message.issueClassification
    ++ (Alpha.encode message.issueSubType
    ++ (Authenticity.encode message.authenticity
    ++ (ShortSaleThresholdIndicator.encode message.shortSaleThresholdIndicator
    ++ (IpoFlag.encode message.ipoFlag
    ++ (LuldReferencePriceTier.encode message.luldReferencePriceTier
    ++ (EtpFlag.encode message.etpFlag
    ++ (encodeUInt 4 message.etpLeverageFactor
    ++ (InverseIndicator.encode message.inverseIndicator
    ++ (Alpha.encode message.bloombergId))))))))))))))

def decode (bytes : List UInt8) : Option (StockDirectoryMessage × List UInt8) := do
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (marketCategory, bytes) ← MarketCategory.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (roundLotsOnly_, bytes) ← RoundLotsOnly.decode bytes
  let (issueClassification, bytes) ← IssueClassification.decode bytes
  let (issueSubType, bytes) ← Alpha.decode 2 bytes
  let (authenticity, bytes) ← Authenticity.decode bytes
  let (shortSaleThresholdIndicator, bytes) ← ShortSaleThresholdIndicator.decode bytes
  let (ipoFlag, bytes) ← IpoFlag.decode bytes
  let (luldReferencePriceTier, bytes) ← LuldReferencePriceTier.decode bytes
  let (etpFlag, bytes) ← EtpFlag.decode bytes
  let (etpLeverageFactor, bytes) ← decodeUInt 4 bytes
  let (inverseIndicator, bytes) ← InverseIndicator.decode bytes
  let (bloombergId, bytes) ← Alpha.decode 12 bytes
  pure ({ stock, marketCategory, financialStatusIndicator, roundLotSize, roundLotsOnly := roundLotsOnly_, issueClassification, issueSubType, authenticity, shortSaleThresholdIndicator, ipoFlag, luldReferencePriceTier, etpFlag, etpLeverageFactor, inverseIndicator, bloombergId }, bytes)

@[simp] theorem encode_length (message : StockDirectoryMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MarketCategory.encode_length, FinancialStatusIndicator.encode_length, encodeUInt_length, RoundLotsOnly.encode_length, IssueClassification.encode_length, Authenticity.encode_length, ShortSaleThresholdIndicator.encode_length, IpoFlag.encode_length, LuldReferencePriceTier.encode_length, EtpFlag.encode_length, InverseIndicator.encode_length]

theorem encode_length_pos (message : StockDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RoundLotsOnly.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IssueClassification.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Authenticity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleThresholdIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IpoFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LuldReferencePriceTier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EtpFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, InverseIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockDirectoryMessage

/-- Reg Sho Short Sale Price Test Restricted Indicator Message: 9 bytes -/
structure RegShoShortSalePriceTestRestrictedIndicatorMessage where
  issueSymbol : Alpha 8
  regShoAction : RegShoAction
  deriving DecidableEq, Repr

namespace RegShoShortSalePriceTestRestrictedIndicatorMessage

def encode (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : List UInt8 :=
  Alpha.encode message.issueSymbol
    ++ (RegShoAction.encode message.regShoAction)

def decode (bytes : List UInt8) : Option (RegShoShortSalePriceTestRestrictedIndicatorMessage × List UInt8) := do
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (regShoAction, bytes) ← RegShoAction.decode bytes
  pure ({ issueSymbol, regShoAction }, bytes)

@[simp] theorem encode_length (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RegShoAction.encode_length]

theorem encode_length_pos (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RegShoAction.decode_encode, some_bind]
  rfl

end RegShoShortSalePriceTestRestrictedIndicatorMessage

/-- Adjusted Closing Price Message: 13 bytes -/
structure AdjustedClosingPriceMessage where
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  adjustedClosingPrice : BitVec 32
  deriving DecidableEq, Repr

namespace AdjustedClosingPriceMessage

def encode (message : AdjustedClosingPriceMessage) : List UInt8 :=
  Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (encodeUInt 4 message.adjustedClosingPrice))

def decode (bytes : List UInt8) : Option (AdjustedClosingPriceMessage × List UInt8) := do
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (adjustedClosingPrice, bytes) ← decodeUInt 4 bytes
  pure ({ issueSymbol, securityClass, adjustedClosingPrice }, bytes)

@[simp] theorem encode_length (message : AdjustedClosingPriceMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AdjustedClosingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdjustedClosingPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AdjustedClosingPriceMessage

/-- Long Form Adjusted Closing Price Message: 17 bytes -/
structure LongFormAdjustedClosingPriceMessage where
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  adjustedClosingPriceLong : BitVec 64
  deriving DecidableEq, Repr

namespace LongFormAdjustedClosingPriceMessage

def encode (message : LongFormAdjustedClosingPriceMessage) : List UInt8 :=
  Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (encodeUInt 8 message.adjustedClosingPriceLong))

def decode (bytes : List UInt8) : Option (LongFormAdjustedClosingPriceMessage × List UInt8) := do
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (adjustedClosingPriceLong, bytes) ← decodeUInt 8 bytes
  pure ({ issueSymbol, securityClass, adjustedClosingPriceLong }, bytes)

@[simp] theorem encode_length (message : LongFormAdjustedClosingPriceMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LongFormAdjustedClosingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongFormAdjustedClosingPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LongFormAdjustedClosingPriceMessage

/-- End Of Day Trade Summary Message: 33 bytes -/
structure EndOfDayTradeSummaryMessage where
  issueSymbol : Alpha 8
  marketCategory : MarketCategory
  consolidatedHighPrice : BitVec 32
  consolidatedLowPrice : BitVec 32
  consolidatedClosingPrice : BitVec 32
  consolidatedVolume : BitVec 64
  consolidatedOpenPrice : BitVec 32
  deriving DecidableEq, Repr

namespace EndOfDayTradeSummaryMessage

def encode (message : EndOfDayTradeSummaryMessage) : List UInt8 :=
  Alpha.encode message.issueSymbol
    ++ (MarketCategory.encode message.marketCategory
    ++ (encodeUInt 4 message.consolidatedHighPrice
    ++ (encodeUInt 4 message.consolidatedLowPrice
    ++ (encodeUInt 4 message.consolidatedClosingPrice
    ++ (encodeUInt 8 message.consolidatedVolume
    ++ (encodeUInt 4 message.consolidatedOpenPrice))))))

def decode (bytes : List UInt8) : Option (EndOfDayTradeSummaryMessage × List UInt8) := do
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (marketCategory, bytes) ← MarketCategory.decode bytes
  let (consolidatedHighPrice, bytes) ← decodeUInt 4 bytes
  let (consolidatedLowPrice, bytes) ← decodeUInt 4 bytes
  let (consolidatedClosingPrice, bytes) ← decodeUInt 4 bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  let (consolidatedOpenPrice, bytes) ← decodeUInt 4 bytes
  pure ({ issueSymbol, marketCategory, consolidatedHighPrice, consolidatedLowPrice, consolidatedClosingPrice, consolidatedVolume, consolidatedOpenPrice }, bytes)

@[simp] theorem encode_length (message : EndOfDayTradeSummaryMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MarketCategory.encode_length, encodeUInt_length]

theorem encode_length_pos (message : EndOfDayTradeSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfDayTradeSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCategory.decode_encode, some_bind]
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

end EndOfDayTradeSummaryMessage

/-- Long Form End Of Day Trade Summary Message: 49 bytes -/
structure LongFormEndOfDayTradeSummaryMessage where
  issueSymbol : Alpha 8
  marketCategory : MarketCategory
  consolidatedHighPriceLong : BitVec 64
  consolidatedLowPriceLong : BitVec 64
  consolidatedClosingPriceLong : BitVec 64
  consolidatedVolume : BitVec 64
  consolidatedOpenPriceLong : BitVec 64
  deriving DecidableEq, Repr

namespace LongFormEndOfDayTradeSummaryMessage

def encode (message : LongFormEndOfDayTradeSummaryMessage) : List UInt8 :=
  Alpha.encode message.issueSymbol
    ++ (MarketCategory.encode message.marketCategory
    ++ (encodeUInt 8 message.consolidatedHighPriceLong
    ++ (encodeUInt 8 message.consolidatedLowPriceLong
    ++ (encodeUInt 8 message.consolidatedClosingPriceLong
    ++ (encodeUInt 8 message.consolidatedVolume
    ++ (encodeUInt 8 message.consolidatedOpenPriceLong))))))

def decode (bytes : List UInt8) : Option (LongFormEndOfDayTradeSummaryMessage × List UInt8) := do
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (marketCategory, bytes) ← MarketCategory.decode bytes
  let (consolidatedHighPriceLong, bytes) ← decodeUInt 8 bytes
  let (consolidatedLowPriceLong, bytes) ← decodeUInt 8 bytes
  let (consolidatedClosingPriceLong, bytes) ← decodeUInt 8 bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  let (consolidatedOpenPriceLong, bytes) ← decodeUInt 8 bytes
  pure ({ issueSymbol, marketCategory, consolidatedHighPriceLong, consolidatedLowPriceLong, consolidatedClosingPriceLong, consolidatedVolume, consolidatedOpenPriceLong }, bytes)

@[simp] theorem encode_length (message : LongFormEndOfDayTradeSummaryMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MarketCategory.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LongFormEndOfDayTradeSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongFormEndOfDayTradeSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCategory.decode_encode, some_bind]
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

end LongFormEndOfDayTradeSummaryMessage

/-- Next Shares End Of Day Trade Summary Message: 49 bytes -/
structure NextSharesEndOfDayTradeSummaryMessage where
  issueSymbol : Alpha 8
  marketCategory : MarketCategory
  consolidatedHighPrice : BitVec 32
  navOffsetAmountHigh : BitVec 32
  consolidatedLowPrice : BitVec 32
  navOffsetAmountLow : BitVec 32
  consolidatedClosingPrice : BitVec 32
  navOffsetAmountClosing : BitVec 32
  consolidatedVolume : BitVec 64
  consolidatedOpenPrice : BitVec 32
  navOffsetAmountOpen : BitVec 32
  deriving DecidableEq, Repr

namespace NextSharesEndOfDayTradeSummaryMessage

def encode (message : NextSharesEndOfDayTradeSummaryMessage) : List UInt8 :=
  Alpha.encode message.issueSymbol
    ++ (MarketCategory.encode message.marketCategory
    ++ (encodeUInt 4 message.consolidatedHighPrice
    ++ (encodeUInt 4 message.navOffsetAmountHigh
    ++ (encodeUInt 4 message.consolidatedLowPrice
    ++ (encodeUInt 4 message.navOffsetAmountLow
    ++ (encodeUInt 4 message.consolidatedClosingPrice
    ++ (encodeUInt 4 message.navOffsetAmountClosing
    ++ (encodeUInt 8 message.consolidatedVolume
    ++ (encodeUInt 4 message.consolidatedOpenPrice
    ++ (encodeUInt 4 message.navOffsetAmountOpen))))))))))

def decode (bytes : List UInt8) : Option (NextSharesEndOfDayTradeSummaryMessage × List UInt8) := do
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (marketCategory, bytes) ← MarketCategory.decode bytes
  let (consolidatedHighPrice, bytes) ← decodeUInt 4 bytes
  let (navOffsetAmountHigh, bytes) ← decodeUInt 4 bytes
  let (consolidatedLowPrice, bytes) ← decodeUInt 4 bytes
  let (navOffsetAmountLow, bytes) ← decodeUInt 4 bytes
  let (consolidatedClosingPrice, bytes) ← decodeUInt 4 bytes
  let (navOffsetAmountClosing, bytes) ← decodeUInt 4 bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  let (consolidatedOpenPrice, bytes) ← decodeUInt 4 bytes
  let (navOffsetAmountOpen, bytes) ← decodeUInt 4 bytes
  pure ({ issueSymbol, marketCategory, consolidatedHighPrice, navOffsetAmountHigh, consolidatedLowPrice, navOffsetAmountLow, consolidatedClosingPrice, navOffsetAmountClosing, consolidatedVolume, consolidatedOpenPrice, navOffsetAmountOpen }, bytes)

@[simp] theorem encode_length (message : NextSharesEndOfDayTradeSummaryMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MarketCategory.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NextSharesEndOfDayTradeSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NextSharesEndOfDayTradeSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCategory.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NextSharesEndOfDayTradeSummaryMessage

/-- Ipo Information Message: 14 bytes -/
structure IpoInformationMessage where
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  referenceForNetChange : ReferenceForNetChange
  referencePrice : BitVec 32
  deriving DecidableEq, Repr

namespace IpoInformationMessage

def encode (message : IpoInformationMessage) : List UInt8 :=
  Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (ReferenceForNetChange.encode message.referenceForNetChange
    ++ (encodeUInt 4 message.referencePrice)))

def decode (bytes : List UInt8) : Option (IpoInformationMessage × List UInt8) := do
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (referenceForNetChange, bytes) ← ReferenceForNetChange.decode bytes
  let (referencePrice, bytes) ← decodeUInt 4 bytes
  pure ({ issueSymbol, securityClass, referenceForNetChange, referencePrice }, bytes)

@[simp] theorem encode_length (message : IpoInformationMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SecurityClass.encode_length, ReferenceForNetChange.encode_length, encodeUInt_length]

theorem encode_length_pos (message : IpoInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IpoInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReferenceForNetChange.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IpoInformationMessage

/-- Mwcb Decline Level Message: 24 bytes -/
structure MwcbDeclineLevelMessage where
  level1 : BitVec 64
  level2 : BitVec 64
  level3 : BitVec 64
  deriving DecidableEq, Repr

namespace MwcbDeclineLevelMessage

def encode (message : MwcbDeclineLevelMessage) : List UInt8 :=
  encodeUInt 8 message.level1
    ++ (encodeUInt 8 message.level2
    ++ (encodeUInt 8 message.level3))

def decode (bytes : List UInt8) : Option (MwcbDeclineLevelMessage × List UInt8) := do
  let (level1, bytes) ← decodeUInt 8 bytes
  let (level2, bytes) ← decodeUInt 8 bytes
  let (level3, bytes) ← decodeUInt 8 bytes
  pure ({ level1, level2, level3 }, bytes)

@[simp] theorem encode_length (message : MwcbDeclineLevelMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : MwcbDeclineLevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MwcbDeclineLevelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MwcbDeclineLevelMessage

/-- Mwcb Status Message: 1 bytes -/
structure MwcbStatusMessage where
  breachedLevel : BreachedLevel
  deriving DecidableEq, Repr

namespace MwcbStatusMessage

def encode (message : MwcbStatusMessage) : List UInt8 :=
  BreachedLevel.encode message.breachedLevel

def decode (bytes : List UInt8) : Option (MwcbStatusMessage × List UInt8) := do
  let (breachedLevel, bytes) ← BreachedLevel.decode bytes
  pure ({ breachedLevel }, bytes)

@[simp] theorem encode_length (message : MwcbStatusMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [BreachedLevel.encode_length]

theorem encode_length_pos (message : MwcbStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MwcbStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [BreachedLevel.decode_encode, some_bind]
  rfl

end MwcbStatusMessage

/-- Ipo Quoting Period Update Message: 17 bytes -/
structure IpoQuotingPeriodUpdateMessage where
  stock : Alpha 8
  ipoQuotationReleaseTime : BitVec 32
  ipoQuotationReleaseQualifier : IpoQuotationReleaseQualifier
  ipoPrice : BitVec 32
  deriving DecidableEq, Repr

namespace IpoQuotingPeriodUpdateMessage

def encode (message : IpoQuotingPeriodUpdateMessage) : List UInt8 :=
  Alpha.encode message.stock
    ++ (encodeUInt 4 message.ipoQuotationReleaseTime
    ++ (IpoQuotationReleaseQualifier.encode message.ipoQuotationReleaseQualifier
    ++ (encodeUInt 4 message.ipoPrice)))

def decode (bytes : List UInt8) : Option (IpoQuotingPeriodUpdateMessage × List UInt8) := do
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (ipoQuotationReleaseTime, bytes) ← decodeUInt 4 bytes
  let (ipoQuotationReleaseQualifier, bytes) ← IpoQuotationReleaseQualifier.decode bytes
  let (ipoPrice, bytes) ← decodeUInt 4 bytes
  pure ({ stock, ipoQuotationReleaseTime, ipoQuotationReleaseQualifier, ipoPrice }, bytes)

@[simp] theorem encode_length (message : IpoQuotingPeriodUpdateMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, IpoQuotationReleaseQualifier.encode_length]

theorem encode_length_pos (message : IpoQuotingPeriodUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IpoQuotingPeriodUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, IpoQuotationReleaseQualifier.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IpoQuotingPeriodUpdateMessage

/-- Operational Halt Message: 10 bytes -/
structure OperationalHaltMessage where
  stock : Alpha 8
  marketCode : MarketCode
  operationalHaltAction : OperationalHaltAction
  deriving DecidableEq, Repr

namespace OperationalHaltMessage

def encode (message : OperationalHaltMessage) : List UInt8 :=
  Alpha.encode message.stock
    ++ (MarketCode.encode message.marketCode
    ++ (OperationalHaltAction.encode message.operationalHaltAction))

def decode (bytes : List UInt8) : Option (OperationalHaltMessage × List UInt8) := do
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (marketCode, bytes) ← MarketCode.decode bytes
  let (operationalHaltAction, bytes) ← OperationalHaltAction.decode bytes
  pure ({ stock, marketCode, operationalHaltAction }, bytes)

@[simp] theorem encode_length (message : OperationalHaltMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MarketCode.encode_length, OperationalHaltAction.encode_length]

theorem encode_length_pos (message : OperationalHaltMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OperationalHaltMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCode.decode_encode, some_bind]
  dsimp only
  rw [OperationalHaltAction.decode_encode, some_bind]
  rfl

end OperationalHaltMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | tradeReportMessage (message : TradeReportMessage) -- "T" 0x54
  | longFormTradeReportMessage (message : LongFormTradeReportMessage) -- "t" 0x74
  | nextSharesTradeReportMessage (message : NextSharesTradeReportMessage) -- "M" 0x4D
  | tradeCancelErrorMessage (message : TradeCancelErrorMessage) -- "X" 0x58
  | longFormTradeCancelErrorMessage (message : LongFormTradeCancelErrorMessage) -- "x" 0x78
  | nextSharesTradeCancelErrorMessage (message : NextSharesTradeCancelErrorMessage) -- "O" 0x4F
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "C" 0x43
  | longFormTradeCorrectionMessage (message : LongFormTradeCorrectionMessage) -- "c" 0x63
  | nextSharesTradeCorrectionMessage (message : NextSharesTradeCorrectionMessage) -- "Z" 0x5A
  | stockTradingActionMessage (message : StockTradingActionMessage) -- "H" 0x48
  | stockDirectoryMessage (message : StockDirectoryMessage) -- "R" 0x52
  | regShoShortSalePriceTestRestrictedIndicatorMessage (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) -- "Y" 0x59
  | adjustedClosingPriceMessage (message : AdjustedClosingPriceMessage) -- "G" 0x47
  | longFormAdjustedClosingPriceMessage (message : LongFormAdjustedClosingPriceMessage) -- "g" 0x67
  | endOfDayTradeSummaryMessage (message : EndOfDayTradeSummaryMessage) -- "J" 0x4A
  | longFormEndOfDayTradeSummaryMessage (message : LongFormEndOfDayTradeSummaryMessage) -- "j" 0x6A
  | nextSharesEndOfDayTradeSummaryMessage (message : NextSharesEndOfDayTradeSummaryMessage) -- "N" 0x4E
  | ipoInformationMessage (message : IpoInformationMessage) -- "I" 0x49
  | mwcbDeclineLevelMessage (message : MwcbDeclineLevelMessage) -- "V" 0x56
  | mwcbStatusMessage (message : MwcbStatusMessage) -- "W" 0x57
  | ipoQuotingPeriodUpdateMessage (message : IpoQuotingPeriodUpdateMessage) -- "K" 0x4B
  | operationalHaltMessage (message : OperationalHaltMessage) -- "h" 0x68
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .tradeReportMessage _ => 84
  | .longFormTradeReportMessage _ => 116
  | .nextSharesTradeReportMessage _ => 77
  | .tradeCancelErrorMessage _ => 88
  | .longFormTradeCancelErrorMessage _ => 120
  | .nextSharesTradeCancelErrorMessage _ => 79
  | .tradeCorrectionMessage _ => 67
  | .longFormTradeCorrectionMessage _ => 99
  | .nextSharesTradeCorrectionMessage _ => 90
  | .stockTradingActionMessage _ => 72
  | .stockDirectoryMessage _ => 82
  | .regShoShortSalePriceTestRestrictedIndicatorMessage _ => 89
  | .adjustedClosingPriceMessage _ => 71
  | .longFormAdjustedClosingPriceMessage _ => 103
  | .endOfDayTradeSummaryMessage _ => 74
  | .longFormEndOfDayTradeSummaryMessage _ => 106
  | .nextSharesEndOfDayTradeSummaryMessage _ => 78
  | .ipoInformationMessage _ => 73
  | .mwcbDeclineLevelMessage _ => 86
  | .mwcbStatusMessage _ => 87
  | .ipoQuotingPeriodUpdateMessage _ => 75
  | .operationalHaltMessage _ => 104

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .tradeReportMessage message => TradeReportMessage.encode message
  | .longFormTradeReportMessage message => LongFormTradeReportMessage.encode message
  | .nextSharesTradeReportMessage message => NextSharesTradeReportMessage.encode message
  | .tradeCancelErrorMessage message => TradeCancelErrorMessage.encode message
  | .longFormTradeCancelErrorMessage message => LongFormTradeCancelErrorMessage.encode message
  | .nextSharesTradeCancelErrorMessage message => NextSharesTradeCancelErrorMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message
  | .longFormTradeCorrectionMessage message => LongFormTradeCorrectionMessage.encode message
  | .nextSharesTradeCorrectionMessage message => NextSharesTradeCorrectionMessage.encode message
  | .stockTradingActionMessage message => StockTradingActionMessage.encode message
  | .stockDirectoryMessage message => StockDirectoryMessage.encode message
  | .regShoShortSalePriceTestRestrictedIndicatorMessage message => RegShoShortSalePriceTestRestrictedIndicatorMessage.encode message
  | .adjustedClosingPriceMessage message => AdjustedClosingPriceMessage.encode message
  | .longFormAdjustedClosingPriceMessage message => LongFormAdjustedClosingPriceMessage.encode message
  | .endOfDayTradeSummaryMessage message => EndOfDayTradeSummaryMessage.encode message
  | .longFormEndOfDayTradeSummaryMessage message => LongFormEndOfDayTradeSummaryMessage.encode message
  | .nextSharesEndOfDayTradeSummaryMessage message => NextSharesEndOfDayTradeSummaryMessage.encode message
  | .ipoInformationMessage message => IpoInformationMessage.encode message
  | .mwcbDeclineLevelMessage message => MwcbDeclineLevelMessage.encode message
  | .mwcbStatusMessage message => MwcbStatusMessage.encode message
  | .ipoQuotingPeriodUpdateMessage message => IpoQuotingPeriodUpdateMessage.encode message
  | .operationalHaltMessage message => OperationalHaltMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 70 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [encode, TradeReportMessage.encode_length]
    omega
  | longFormTradeReportMessage inner =>
    simp only [encode, LongFormTradeReportMessage.encode_length]
    omega
  | nextSharesTradeReportMessage inner =>
    simp only [encode, NextSharesTradeReportMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [encode, TradeCancelErrorMessage.encode_length]
    omega
  | longFormTradeCancelErrorMessage inner =>
    simp only [encode, LongFormTradeCancelErrorMessage.encode_length]
    omega
  | nextSharesTradeCancelErrorMessage inner =>
    simp only [encode, NextSharesTradeCancelErrorMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega
  | longFormTradeCorrectionMessage inner =>
    simp only [encode, LongFormTradeCorrectionMessage.encode_length]
    omega
  | nextSharesTradeCorrectionMessage inner =>
    simp only [encode, NextSharesTradeCorrectionMessage.encode_length]
    omega
  | stockTradingActionMessage inner =>
    simp only [encode, StockTradingActionMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [encode, StockDirectoryMessage.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [encode, RegShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | adjustedClosingPriceMessage inner =>
    simp only [encode, AdjustedClosingPriceMessage.encode_length]
    omega
  | longFormAdjustedClosingPriceMessage inner =>
    simp only [encode, LongFormAdjustedClosingPriceMessage.encode_length]
    omega
  | endOfDayTradeSummaryMessage inner =>
    simp only [encode, EndOfDayTradeSummaryMessage.encode_length]
    omega
  | longFormEndOfDayTradeSummaryMessage inner =>
    simp only [encode, LongFormEndOfDayTradeSummaryMessage.encode_length]
    omega
  | nextSharesEndOfDayTradeSummaryMessage inner =>
    simp only [encode, NextSharesEndOfDayTradeSummaryMessage.encode_length]
    omega
  | ipoInformationMessage inner =>
    simp only [encode, IpoInformationMessage.encode_length]
    omega
  | mwcbDeclineLevelMessage inner =>
    simp only [encode, MwcbDeclineLevelMessage.encode_length]
    omega
  | mwcbStatusMessage inner =>
    simp only [encode, MwcbStatusMessage.encode_length]
    omega
  | ipoQuotingPeriodUpdateMessage inner =>
    simp only [encode, IpoQuotingPeriodUpdateMessage.encode_length]
    omega
  | operationalHaltMessage inner =>
    simp only [encode, OperationalHaltMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 84 then (TradeReportMessage.decode bytes).map fun (message, rest) => (.tradeReportMessage message, rest)
  else if tag = 116 then (LongFormTradeReportMessage.decode bytes).map fun (message, rest) => (.longFormTradeReportMessage message, rest)
  else if tag = 77 then (NextSharesTradeReportMessage.decode bytes).map fun (message, rest) => (.nextSharesTradeReportMessage message, rest)
  else if tag = 88 then (TradeCancelErrorMessage.decode bytes).map fun (message, rest) => (.tradeCancelErrorMessage message, rest)
  else if tag = 120 then (LongFormTradeCancelErrorMessage.decode bytes).map fun (message, rest) => (.longFormTradeCancelErrorMessage message, rest)
  else if tag = 79 then (NextSharesTradeCancelErrorMessage.decode bytes).map fun (message, rest) => (.nextSharesTradeCancelErrorMessage message, rest)
  else if tag = 67 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else if tag = 99 then (LongFormTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.longFormTradeCorrectionMessage message, rest)
  else if tag = 90 then (NextSharesTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.nextSharesTradeCorrectionMessage message, rest)
  else if tag = 72 then (StockTradingActionMessage.decode bytes).map fun (message, rest) => (.stockTradingActionMessage message, rest)
  else if tag = 82 then (StockDirectoryMessage.decode bytes).map fun (message, rest) => (.stockDirectoryMessage message, rest)
  else if tag = 89 then (RegShoShortSalePriceTestRestrictedIndicatorMessage.decode bytes).map fun (message, rest) => (.regShoShortSalePriceTestRestrictedIndicatorMessage message, rest)
  else if tag = 71 then (AdjustedClosingPriceMessage.decode bytes).map fun (message, rest) => (.adjustedClosingPriceMessage message, rest)
  else if tag = 103 then (LongFormAdjustedClosingPriceMessage.decode bytes).map fun (message, rest) => (.longFormAdjustedClosingPriceMessage message, rest)
  else if tag = 74 then (EndOfDayTradeSummaryMessage.decode bytes).map fun (message, rest) => (.endOfDayTradeSummaryMessage message, rest)
  else if tag = 106 then (LongFormEndOfDayTradeSummaryMessage.decode bytes).map fun (message, rest) => (.longFormEndOfDayTradeSummaryMessage message, rest)
  else if tag = 78 then (NextSharesEndOfDayTradeSummaryMessage.decode bytes).map fun (message, rest) => (.nextSharesEndOfDayTradeSummaryMessage message, rest)
  else if tag = 73 then (IpoInformationMessage.decode bytes).map fun (message, rest) => (.ipoInformationMessage message, rest)
  else if tag = 86 then (MwcbDeclineLevelMessage.decode bytes).map fun (message, rest) => (.mwcbDeclineLevelMessage message, rest)
  else if tag = 87 then (MwcbStatusMessage.decode bytes).map fun (message, rest) => (.mwcbStatusMessage message, rest)
  else if tag = 75 then (IpoQuotingPeriodUpdateMessage.decode bytes).map fun (message, rest) => (.ipoQuotingPeriodUpdateMessage message, rest)
  else if tag = 104 then (OperationalHaltMessage.decode bytes).map fun (message, rest) => (.operationalHaltMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ trackingNumber, timestamp, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradeReportMessage.encode_length]
    omega
  | longFormTradeReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LongFormTradeReportMessage.encode_length]
    omega
  | nextSharesTradeReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, NextSharesTradeReportMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradeCancelErrorMessage.encode_length]
    omega
  | longFormTradeCancelErrorMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LongFormTradeCancelErrorMessage.encode_length]
    omega
  | nextSharesTradeCancelErrorMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, NextSharesTradeCancelErrorMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradeCorrectionMessage.encode_length]
    omega
  | longFormTradeCorrectionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LongFormTradeCorrectionMessage.encode_length]
    omega
  | nextSharesTradeCorrectionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, NextSharesTradeCorrectionMessage.encode_length]
    omega
  | stockTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StockTradingActionMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StockDirectoryMessage.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RegShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | adjustedClosingPriceMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, AdjustedClosingPriceMessage.encode_length]
    omega
  | longFormAdjustedClosingPriceMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LongFormAdjustedClosingPriceMessage.encode_length]
    omega
  | endOfDayTradeSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, EndOfDayTradeSummaryMessage.encode_length]
    omega
  | longFormEndOfDayTradeSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LongFormEndOfDayTradeSummaryMessage.encode_length]
    omega
  | nextSharesEndOfDayTradeSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, NextSharesEndOfDayTradeSummaryMessage.encode_length]
    omega
  | ipoInformationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, IpoInformationMessage.encode_length]
    omega
  | mwcbDeclineLevelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MwcbDeclineLevelMessage.encode_length]
    omega
  | mwcbStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MwcbStatusMessage.encode_length]
    omega
  | ipoQuotingPeriodUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, IpoQuotingPeriodUpdateMessage.encode_length]
    omega
  | operationalHaltMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OperationalHaltMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NasdaqNsmequitiesNlsplusItchV30
