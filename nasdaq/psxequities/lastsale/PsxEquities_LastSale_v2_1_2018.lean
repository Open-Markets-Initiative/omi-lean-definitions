import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Last Sale v2.1.2018

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqPsxequitiesLastsaleItchV212018

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x51, 0x53, 0x4D, 0x45, 0x43]

inductive EventCode where
  | startOfTransmissions -- Start Of Transmissions
  | startOfMarketHours -- Start Of Market Hours
  | startOfSystemHours -- Start Of System Hours
  | endOfMarketHours -- End Of Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfTransmissions -- End Of Transmissions
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfTransmissions => 0x4F
  | .startOfMarketHours => 0x51
  | .startOfSystemHours => 0x53
  | .endOfMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfTransmissions => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfTransmissions
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x45 then .endOfSystemHours
  else .endOfTransmissions

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfTransmissions => decide
  | startOfMarketHours => decide
  | startOfSystemHours => decide
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

/-- Market Center Identifier: one byte code -/
def MarketCenterIdentifier.codes : List UInt8 :=
  [0x42, 0x58]

inductive MarketCenterIdentifier where
  | psxExecutionSystem -- Psx Execution System
  | psxExecutionSystem_58 -- Psx Execution System
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCenterIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCenterIdentifier

def toByte : MarketCenterIdentifier → UInt8
  | .psxExecutionSystem => 0x42
  | .psxExecutionSystem_58 => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCenterIdentifier :=
  if byte = 0x42 then .psxExecutionSystem
  else .psxExecutionSystem_58

def ofByte (byte : UInt8) : MarketCenterIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCenterIdentifier) : ofByte value.toByte = value := by
  cases value with
  | psxExecutionSystem => decide
  | psxExecutionSystem_58 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCenterIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCenterIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCenterIdentifier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCenterIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCenterIdentifier

/-- Security Class: one byte code -/
def SecurityClass.codes : List UInt8 :=
  [0x51, 0x4E, 0x41, 0x50, 0x5A, 0x56]

inductive SecurityClass where
  | nasdaq -- Nasdaq
  | nyse -- Nyse
  | nyseAmex -- Nyse Amex
  | nyseArca -- Nyse Arca
  | bats -- Bats
  | investorsExchange -- Investors Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityClass.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityClass

def toByte : SecurityClass → UInt8
  | .nasdaq => 0x51
  | .nyse => 0x4E
  | .nyseAmex => 0x41
  | .nyseArca => 0x50
  | .bats => 0x5A
  | .investorsExchange => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityClass :=
  if byte = 0x51 then .nasdaq
  else if byte = 0x4E then .nyse
  else if byte = 0x41 then .nyseAmex
  else if byte = 0x50 then .nyseArca
  else if byte = 0x5A then .bats
  else .investorsExchange

def ofByte (byte : UInt8) : SecurityClass :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityClass) : ofByte value.toByte = value := by
  cases value with
  | nasdaq => decide
  | nyse => decide
  | nyseAmex => decide
  | nyseArca => decide
  | bats => decide
  | investorsExchange => decide
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

/-- Sale Condition Modifier Level 1: one byte code -/
def SaleConditionModifierLevel1.codes : List UInt8 :=
  [0x4A, 0x40, 0x43, 0x4E, 0x52]

inductive SaleConditionModifierLevel1 where
  | proxyPriceSettlement -- Proxy Price Settlement
  | regularSettlement -- Regular Settlement
  | cashSettlement -- Cash Settlement
  | nextDaySettlement -- Next Day Settlement
  | sellerSettlement -- Seller Settlement
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleConditionModifierLevel1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleConditionModifierLevel1

def toByte : SaleConditionModifierLevel1 → UInt8
  | .proxyPriceSettlement => 0x4A
  | .regularSettlement => 0x40
  | .cashSettlement => 0x43
  | .nextDaySettlement => 0x4E
  | .sellerSettlement => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleConditionModifierLevel1 :=
  if byte = 0x4A then .proxyPriceSettlement
  else if byte = 0x40 then .regularSettlement
  else if byte = 0x43 then .cashSettlement
  else if byte = 0x4E then .nextDaySettlement
  else .sellerSettlement

def ofByte (byte : UInt8) : SaleConditionModifierLevel1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleConditionModifierLevel1) : ofByte value.toByte = value := by
  cases value with
  | proxyPriceSettlement => decide
  | regularSettlement => decide
  | cashSettlement => decide
  | nextDaySettlement => decide
  | sellerSettlement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleConditionModifierLevel1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleConditionModifierLevel1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleConditionModifierLevel1) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SaleConditionModifierLevel1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleConditionModifierLevel1

/-- Sale Condition Modifier Level 2: one byte code -/
def SaleConditionModifierLevel2.codes : List UInt8 :=
  [0x46, 0x4F, 0x34, 0x35, 0x36, 0x20]

inductive SaleConditionModifierLevel2 where
  | intermarketSweep -- Intermarket Sweep
  | openingPrint -- Opening Print
  | derivativePriced -- Derivative Priced
  | reOpeningPrint -- Re Opening Print
  | closingPrint -- Closing Print
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleConditionModifierLevel2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleConditionModifierLevel2

def toByte : SaleConditionModifierLevel2 → UInt8
  | .intermarketSweep => 0x46
  | .openingPrint => 0x4F
  | .derivativePriced => 0x34
  | .reOpeningPrint => 0x35
  | .closingPrint => 0x36
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleConditionModifierLevel2 :=
  if byte = 0x46 then .intermarketSweep
  else if byte = 0x4F then .openingPrint
  else if byte = 0x34 then .derivativePriced
  else if byte = 0x35 then .reOpeningPrint
  else if byte = 0x36 then .closingPrint
  else .notApplicable

def ofByte (byte : UInt8) : SaleConditionModifierLevel2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleConditionModifierLevel2) : ofByte value.toByte = value := by
  cases value with
  | intermarketSweep => decide
  | openingPrint => decide
  | derivativePriced => decide
  | reOpeningPrint => decide
  | closingPrint => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleConditionModifierLevel2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleConditionModifierLevel2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleConditionModifierLevel2) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SaleConditionModifierLevel2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleConditionModifierLevel2

/-- Sale Condition Modifier Level 3: one byte code -/
def SaleConditionModifierLevel3.codes : List UInt8 :=
  [0x54, 0x55, 0x4C, 0x5A, 0x20]

inductive SaleConditionModifierLevel3 where
  | extendedHoursTrade -- Extended Hours Trade
  | reportedLateOrOutOfSequence -- Reported Late Or Out Of Sequence
  | reportedLateButInSequence -- Reported Late But In Sequence
  | soldOutOfSequence -- Sold Out Of Sequence
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleConditionModifierLevel3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleConditionModifierLevel3

def toByte : SaleConditionModifierLevel3 → UInt8
  | .extendedHoursTrade => 0x54
  | .reportedLateOrOutOfSequence => 0x55
  | .reportedLateButInSequence => 0x4C
  | .soldOutOfSequence => 0x5A
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleConditionModifierLevel3 :=
  if byte = 0x54 then .extendedHoursTrade
  else if byte = 0x55 then .reportedLateOrOutOfSequence
  else if byte = 0x4C then .reportedLateButInSequence
  else if byte = 0x5A then .soldOutOfSequence
  else .notApplicable

def ofByte (byte : UInt8) : SaleConditionModifierLevel3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleConditionModifierLevel3) : ofByte value.toByte = value := by
  cases value with
  | extendedHoursTrade => decide
  | reportedLateOrOutOfSequence => decide
  | reportedLateButInSequence => decide
  | soldOutOfSequence => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleConditionModifierLevel3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleConditionModifierLevel3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleConditionModifierLevel3) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SaleConditionModifierLevel3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleConditionModifierLevel3

/-- Sale Condition Modifier Level 4: one byte code -/
def SaleConditionModifierLevel4.codes : List UInt8 :=
  [0x41, 0x42, 0x44, 0x48, 0x4D, 0x50, 0x51, 0x53, 0x57, 0x58, 0x6F, 0x78, 0x20]

inductive SaleConditionModifierLevel4 where
  | acquisition -- Acquisition
  | bunched -- Bunched
  | distribution -- Distribution
  | priceVariationTransaction -- Price Variation Transaction
  | psxOfficialClosePrice -- Psx Official Close Price
  | priorReferencePrice -- Prior Reference Price
  | psxOfficialOpeningPrice -- Psx Official Opening Price
  | splitTrade -- Split Trade
  | weightedAveragePrice -- Weighted Average Price
  | crossTrade -- Cross Trade
  | oddLotExecution -- Odd Lot Execution
  | oddLotCrossExecution -- Odd Lot Cross Execution
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleConditionModifierLevel4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleConditionModifierLevel4

def toByte : SaleConditionModifierLevel4 → UInt8
  | .acquisition => 0x41
  | .bunched => 0x42
  | .distribution => 0x44
  | .priceVariationTransaction => 0x48
  | .psxOfficialClosePrice => 0x4D
  | .priorReferencePrice => 0x50
  | .psxOfficialOpeningPrice => 0x51
  | .splitTrade => 0x53
  | .weightedAveragePrice => 0x57
  | .crossTrade => 0x58
  | .oddLotExecution => 0x6F
  | .oddLotCrossExecution => 0x78
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleConditionModifierLevel4 :=
  if byte = 0x41 then .acquisition
  else if byte = 0x42 then .bunched
  else if byte = 0x44 then .distribution
  else if byte = 0x48 then .priceVariationTransaction
  else if byte = 0x4D then .psxOfficialClosePrice
  else if byte = 0x50 then .priorReferencePrice
  else if byte = 0x51 then .psxOfficialOpeningPrice
  else if byte = 0x53 then .splitTrade
  else if byte = 0x57 then .weightedAveragePrice
  else if byte = 0x58 then .crossTrade
  else if byte = 0x6F then .oddLotExecution
  else if byte = 0x78 then .oddLotCrossExecution
  else .notApplicable

def ofByte (byte : UInt8) : SaleConditionModifierLevel4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleConditionModifierLevel4) : ofByte value.toByte = value := by
  cases value with
  | acquisition => decide
  | bunched => decide
  | distribution => decide
  | priceVariationTransaction => decide
  | psxOfficialClosePrice => decide
  | priorReferencePrice => decide
  | psxOfficialOpeningPrice => decide
  | splitTrade => decide
  | weightedAveragePrice => decide
  | crossTrade => decide
  | oddLotExecution => decide
  | oddLotCrossExecution => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleConditionModifierLevel4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleConditionModifierLevel4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleConditionModifierLevel4) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SaleConditionModifierLevel4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleConditionModifierLevel4

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x48, 0x51, 0x54]

inductive CurrentTradingState where
  | halted -- Halted
  | quotationOnly -- Quotation Only
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .halted => 0x48
  | .quotationOnly => 0x51
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .halted
  else if byte = 0x51 then .quotationOnly
  else .trading

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
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

/-- Reg Sho Action: one byte code -/
def RegShoAction.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive RegShoAction where
  | noPriceTest -- No Price Test
  | regShoShortSalePriceTestRestriction -- Reg Sho Short Sale Price Test Restriction
  | testRestrictionRemains -- Test Restriction Remains
  | unlisted (byte : { byte : UInt8 // byte ∉ RegShoAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RegShoAction

def toByte : RegShoAction → UInt8
  | .noPriceTest => 0x30
  | .regShoShortSalePriceTestRestriction => 0x31
  | .testRestrictionRemains => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RegShoAction :=
  if byte = 0x30 then .noPriceTest
  else if byte = 0x31 then .regShoShortSalePriceTestRestriction
  else .testRestrictionRemains

def ofByte (byte : UInt8) : RegShoAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RegShoAction) : ofByte value.toByte = value := by
  cases value with
  | noPriceTest => decide
  | regShoShortSalePriceTestRestriction => decide
  | testRestrictionRemains => decide
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

/-- Market Category: one byte code -/
def MarketCategory.codes : List UInt8 :=
  [0x51, 0x47, 0x53, 0x4E, 0x41, 0x50, 0x5A, 0x56, 0x20]

inductive MarketCategory where
  | nasdaqGlobalSelectMarket -- Nasdaq Global Select Market
  | nasdaqGlobalMarket -- Nasdaq Global Market
  | nasdaqCapitalMarket -- Nasdaq Capital Market
  | nyse -- Nyse
  | nyseMkt -- Nyse Mkt
  | nyseArca -- Nyse Arca
  | batsZ -- Bats Z
  | investorsExchange -- Investors Exchange
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCategory

def toByte : MarketCategory → UInt8
  | .nasdaqGlobalSelectMarket => 0x51
  | .nasdaqGlobalMarket => 0x47
  | .nasdaqCapitalMarket => 0x53
  | .nyse => 0x4E
  | .nyseMkt => 0x41
  | .nyseArca => 0x50
  | .batsZ => 0x5A
  | .investorsExchange => 0x56
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCategory :=
  if byte = 0x51 then .nasdaqGlobalSelectMarket
  else if byte = 0x47 then .nasdaqGlobalMarket
  else if byte = 0x53 then .nasdaqCapitalMarket
  else if byte = 0x4E then .nyse
  else if byte = 0x41 then .nyseMkt
  else if byte = 0x50 then .nyseArca
  else if byte = 0x5A then .batsZ
  else if byte = 0x56 then .investorsExchange
  else .notAvailable

def ofByte (byte : UInt8) : MarketCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCategory) : ofByte value.toByte = value := by
  cases value with
  | nasdaqGlobalSelectMarket => decide
  | nasdaqGlobalMarket => decide
  | nasdaqCapitalMarket => decide
  | nyse => decide
  | nyseMkt => decide
  | nyseArca => decide
  | batsZ => decide
  | investorsExchange => decide
  | notAvailable => decide
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
  | creationsAndRedemptionsSuspended -- Creations And Redemptions Suspended
  | normal -- Normal
  | na -- Na
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
  | .creationsAndRedemptionsSuspended => 0x43
  | .normal => 0x4E
  | .na => 0x20
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
  else if byte = 0x43 then .creationsAndRedemptionsSuspended
  else if byte = 0x4E then .normal
  else .na

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
  | creationsAndRedemptionsSuspended => decide
  | normal => decide
  | na => decide
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
  | common -- Common
  | depository -- Depository
  | sec144A -- Sec 144 A
  | limited -- Limited
  | notes -- Notes
  | ordinaryShare -- Ordinary Share
  | preferred -- Preferred
  | other -- Other
  | right -- Right
  | shares -- Shares
  | convertible -- Convertible
  | unit -- Unit
  | unitsBenifInt -- Units Benif Int
  | warrant -- Warrant
  | unlisted (byte : { byte : UInt8 // byte ∉ IssueClassification.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IssueClassification

def toByte : IssueClassification → UInt8
  | .americanDepositaryShare => 0x41
  | .bond => 0x42
  | .common => 0x43
  | .depository => 0x46
  | .sec144A => 0x49
  | .limited => 0x4C
  | .notes => 0x4E
  | .ordinaryShare => 0x4F
  | .preferred => 0x50
  | .other => 0x51
  | .right => 0x52
  | .shares => 0x53
  | .convertible => 0x54
  | .unit => 0x55
  | .unitsBenifInt => 0x56
  | .warrant => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IssueClassification :=
  if byte = 0x41 then .americanDepositaryShare
  else if byte = 0x42 then .bond
  else if byte = 0x43 then .common
  else if byte = 0x46 then .depository
  else if byte = 0x49 then .sec144A
  else if byte = 0x4C then .limited
  else if byte = 0x4E then .notes
  else if byte = 0x4F then .ordinaryShare
  else if byte = 0x50 then .preferred
  else if byte = 0x51 then .other
  else if byte = 0x52 then .right
  else if byte = 0x53 then .shares
  else if byte = 0x54 then .convertible
  else if byte = 0x55 then .unit
  else if byte = 0x56 then .unitsBenifInt
  else .warrant

def ofByte (byte : UInt8) : IssueClassification :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IssueClassification) : ofByte value.toByte = value := by
  cases value with
  | americanDepositaryShare => decide
  | bond => decide
  | common => decide
  | depository => decide
  | sec144A => decide
  | limited => decide
  | notes => decide
  | ordinaryShare => decide
  | preferred => decide
  | other => decide
  | right => decide
  | shares => decide
  | convertible => decide
  | unit => decide
  | unitsBenifInt => decide
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
  | liveProduction -- Live Production
  | test -- Test
  | unlisted (byte : { byte : UInt8 // byte ∉ Authenticity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Authenticity

def toByte : Authenticity → UInt8
  | .liveProduction => 0x50
  | .test => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Authenticity :=
  if byte = 0x50 then .liveProduction
  else .test

def ofByte (byte : UInt8) : Authenticity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Authenticity) : ofByte value.toByte = value := by
  cases value with
  | liveProduction => decide
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
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSaleThresholdIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSaleThresholdIndicator

def toByte : ShortSaleThresholdIndicator → UInt8
  | .restricted => 0x59
  | .notRestricted => 0x4E
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSaleThresholdIndicator :=
  if byte = 0x59 then .restricted
  else if byte = 0x4E then .notRestricted
  else .na

def ofByte (byte : UInt8) : ShortSaleThresholdIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSaleThresholdIndicator) : ofByte value.toByte = value := by
  cases value with
  | restricted => decide
  | notRestricted => decide
  | na => decide
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
  | nasdaqListedInstrument -- Nasdaq Listed Instrument
  | nasdaqListedInstrument_4e -- Nasdaq Listed Instrument
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ IpoFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IpoFlag

def toByte : IpoFlag → UInt8
  | .nasdaqListedInstrument => 0x59
  | .nasdaqListedInstrument_4e => 0x4E
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IpoFlag :=
  if byte = 0x59 then .nasdaqListedInstrument
  else if byte = 0x4E then .nasdaqListedInstrument_4e
  else .na

def ofByte (byte : UInt8) : IpoFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IpoFlag) : ofByte value.toByte = value := by
  cases value with
  | nasdaqListedInstrument => decide
  | nasdaqListedInstrument_4e => decide
  | na => decide
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
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ LuldReferencePriceTier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LuldReferencePriceTier

def toByte : LuldReferencePriceTier → UInt8
  | .tier1 => 0x31
  | .tier2 => 0x32
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LuldReferencePriceTier :=
  if byte = 0x31 then .tier1
  else if byte = 0x32 then .tier2
  else .na

def ofByte (byte : UInt8) : LuldReferencePriceTier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LuldReferencePriceTier) : ofByte value.toByte = value := by
  cases value with
  | tier1 => decide
  | tier2 => decide
  | na => decide
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
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ EtpFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EtpFlag

def toByte : EtpFlag → UInt8
  | .etp => 0x59
  | .notEtp => 0x4E
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EtpFlag :=
  if byte = 0x59 then .etp
  else if byte = 0x4E then .notEtp
  else .na

def ofByte (byte : UInt8) : EtpFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EtpFlag) : ofByte value.toByte = value := by
  cases value with
  | etp => decide
  | notEtp => decide
  | na => decide
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
  | inverseEtp -- Inverse Etp
  | notInverseEtp -- Not Inverse Etp
  | unlisted (byte : { byte : UInt8 // byte ∉ InverseIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InverseIndicator

def toByte : InverseIndicator → UInt8
  | .inverseEtp => 0x59
  | .notInverseEtp => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InverseIndicator :=
  if byte = 0x59 then .inverseEtp
  else .notInverseEtp

def ofByte (byte : UInt8) : InverseIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InverseIndicator) : ofByte value.toByte = value := by
  cases value with
  | inverseEtp => decide
  | notInverseEtp => decide
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
  | resumed -- Resumed
  | unlisted (byte : { byte : UInt8 // byte ∉ OperationalHaltAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OperationalHaltAction

def toByte : OperationalHaltAction → UInt8
  | .halted => 0x48
  | .resumed => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OperationalHaltAction :=
  if byte = 0x48 then .halted
  else .resumed

def ofByte (byte : UInt8) : OperationalHaltAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OperationalHaltAction) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | resumed => decide
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

/-- Trade Report Message: 32 bytes -/
structure TradeReportMessage where
  marketCenterIdentifier : MarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  tradeControlNumber : Alpha 10
  tradePrice : BitVec 32
  tradeSize : BitVec 32
  saleConditionModifierLevel1 : SaleConditionModifierLevel1
  saleConditionModifierLevel2 : SaleConditionModifierLevel2
  saleConditionModifierLevel3 : SaleConditionModifierLevel3
  saleConditionModifierLevel4 : SaleConditionModifierLevel4
  deriving DecidableEq, Repr

namespace TradeReportMessage

def encode (message : TradeReportMessage) : List UInt8 :=
  MarketCenterIdentifier.encode message.marketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.tradeControlNumber
    ++ (encodeUInt 4 message.tradePrice
    ++ (encodeUInt 4 message.tradeSize
    ++ (SaleConditionModifierLevel1.encode message.saleConditionModifierLevel1
    ++ (SaleConditionModifierLevel2.encode message.saleConditionModifierLevel2
    ++ (SaleConditionModifierLevel3.encode message.saleConditionModifierLevel3
    ++ (SaleConditionModifierLevel4.encode message.saleConditionModifierLevel4)))))))))

def decode (bytes : List UInt8) : Option (TradeReportMessage × List UInt8) := do
  let (marketCenterIdentifier, bytes) ← MarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (tradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (tradeSize, bytes) ← decodeUInt 4 bytes
  let (saleConditionModifierLevel1, bytes) ← SaleConditionModifierLevel1.decode bytes
  let (saleConditionModifierLevel2, bytes) ← SaleConditionModifierLevel2.decode bytes
  let (saleConditionModifierLevel3, bytes) ← SaleConditionModifierLevel3.decode bytes
  let (saleConditionModifierLevel4, bytes) ← SaleConditionModifierLevel4.decode bytes
  pure ({ marketCenterIdentifier, issueSymbol, securityClass, tradeControlNumber, tradePrice, tradeSize, saleConditionModifierLevel1, saleConditionModifierLevel2, saleConditionModifierLevel3, saleConditionModifierLevel4 }, bytes)

@[simp] theorem encode_length (message : TradeReportMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, MarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length, SaleConditionModifierLevel1.encode_length, SaleConditionModifierLevel2.encode_length, SaleConditionModifierLevel3.encode_length, SaleConditionModifierLevel4.encode_length]

theorem encode_length_pos (message : TradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketCenterIdentifier.decode_encode, some_bind]
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
  rw [List.append_assoc, SaleConditionModifierLevel1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditionModifierLevel2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditionModifierLevel3.decode_encode, some_bind]
  dsimp only
  rw [SaleConditionModifierLevel4.decode_encode, some_bind]
  rfl

end TradeReportMessage

/-- Next Shares Trade Report Message: 36 bytes -/
structure NextSharesTradeReportMessage where
  marketCenterIdentifier : MarketCenterIdentifier
  nextSharesSymbol : Alpha 8
  securityClass : SecurityClass
  tradeControlNumber : Alpha 10
  proxyPrice : BitVec 32
  tradeSize : BitVec 32
  navPremiumDiscountAmount : BitVec 32
  saleConditionModifierLevel1 : SaleConditionModifierLevel1
  saleConditionModifierLevel2 : SaleConditionModifierLevel2
  saleConditionModifierLevel3 : SaleConditionModifierLevel3
  saleConditionModifierLevel4 : SaleConditionModifierLevel4
  deriving DecidableEq, Repr

namespace NextSharesTradeReportMessage

def encode (message : NextSharesTradeReportMessage) : List UInt8 :=
  MarketCenterIdentifier.encode message.marketCenterIdentifier
    ++ (Alpha.encode message.nextSharesSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.tradeControlNumber
    ++ (encodeUInt 4 message.proxyPrice
    ++ (encodeUInt 4 message.tradeSize
    ++ (encodeUInt 4 message.navPremiumDiscountAmount
    ++ (SaleConditionModifierLevel1.encode message.saleConditionModifierLevel1
    ++ (SaleConditionModifierLevel2.encode message.saleConditionModifierLevel2
    ++ (SaleConditionModifierLevel3.encode message.saleConditionModifierLevel3
    ++ (SaleConditionModifierLevel4.encode message.saleConditionModifierLevel4))))))))))

def decode (bytes : List UInt8) : Option (NextSharesTradeReportMessage × List UInt8) := do
  let (marketCenterIdentifier, bytes) ← MarketCenterIdentifier.decode bytes
  let (nextSharesSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (tradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (proxyPrice, bytes) ← decodeUInt 4 bytes
  let (tradeSize, bytes) ← decodeUInt 4 bytes
  let (navPremiumDiscountAmount, bytes) ← decodeUInt 4 bytes
  let (saleConditionModifierLevel1, bytes) ← SaleConditionModifierLevel1.decode bytes
  let (saleConditionModifierLevel2, bytes) ← SaleConditionModifierLevel2.decode bytes
  let (saleConditionModifierLevel3, bytes) ← SaleConditionModifierLevel3.decode bytes
  let (saleConditionModifierLevel4, bytes) ← SaleConditionModifierLevel4.decode bytes
  pure ({ marketCenterIdentifier, nextSharesSymbol, securityClass, tradeControlNumber, proxyPrice, tradeSize, navPremiumDiscountAmount, saleConditionModifierLevel1, saleConditionModifierLevel2, saleConditionModifierLevel3, saleConditionModifierLevel4 }, bytes)

@[simp] theorem encode_length (message : NextSharesTradeReportMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, MarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length, SaleConditionModifierLevel1.encode_length, SaleConditionModifierLevel2.encode_length, SaleConditionModifierLevel3.encode_length, SaleConditionModifierLevel4.encode_length]

theorem encode_length_pos (message : NextSharesTradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NextSharesTradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketCenterIdentifier.decode_encode, some_bind]
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
  rw [List.append_assoc, SaleConditionModifierLevel1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditionModifierLevel2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditionModifierLevel3.decode_encode, some_bind]
  dsimp only
  rw [SaleConditionModifierLevel4.decode_encode, some_bind]
  rfl

end NextSharesTradeReportMessage

/-- Trade Cancel Error Message: 32 bytes -/
structure TradeCancelErrorMessage where
  marketCenterIdentifier : MarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  originalTradeControlNumber : Alpha 10
  originalTradePrice : BitVec 32
  originalTradeSize : BitVec 32
  originalSaleConditionModifier : Alpha 4
  deriving DecidableEq, Repr

namespace TradeCancelErrorMessage

def encode (message : TradeCancelErrorMessage) : List UInt8 :=
  MarketCenterIdentifier.encode message.marketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.originalTradeControlNumber
    ++ (encodeUInt 4 message.originalTradePrice
    ++ (encodeUInt 4 message.originalTradeSize
    ++ (Alpha.encode message.originalSaleConditionModifier))))))

def decode (bytes : List UInt8) : Option (TradeCancelErrorMessage × List UInt8) := do
  let (marketCenterIdentifier, bytes) ← MarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (originalTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (originalTradePrice, bytes) ← decodeUInt 4 bytes
  let (originalTradeSize, bytes) ← decodeUInt 4 bytes
  let (originalSaleConditionModifier, bytes) ← Alpha.decode 4 bytes
  pure ({ marketCenterIdentifier, issueSymbol, securityClass, originalTradeControlNumber, originalTradePrice, originalTradeSize, originalSaleConditionModifier }, bytes)

@[simp] theorem encode_length (message : TradeCancelErrorMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, MarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeCancelErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketCenterIdentifier.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCancelErrorMessage

/-- Trade Cancel Error For Next Shares Message: 36 bytes -/
structure TradeCancelErrorForNextSharesMessage where
  marketCenterIdentifier : MarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  originalTradeControlNumber : Alpha 10
  originalTradePrice : BitVec 32
  originalNavPremiumDiscountAmount : BitVec 32
  originalTradeSize : BitVec 32
  originalSaleConditionModifier : Alpha 4
  deriving DecidableEq, Repr

namespace TradeCancelErrorForNextSharesMessage

def encode (message : TradeCancelErrorForNextSharesMessage) : List UInt8 :=
  MarketCenterIdentifier.encode message.marketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.originalTradeControlNumber
    ++ (encodeUInt 4 message.originalTradePrice
    ++ (encodeUInt 4 message.originalNavPremiumDiscountAmount
    ++ (encodeUInt 4 message.originalTradeSize
    ++ (Alpha.encode message.originalSaleConditionModifier)))))))

def decode (bytes : List UInt8) : Option (TradeCancelErrorForNextSharesMessage × List UInt8) := do
  let (marketCenterIdentifier, bytes) ← MarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (originalTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (originalTradePrice, bytes) ← decodeUInt 4 bytes
  let (originalNavPremiumDiscountAmount, bytes) ← decodeUInt 4 bytes
  let (originalTradeSize, bytes) ← decodeUInt 4 bytes
  let (originalSaleConditionModifier, bytes) ← Alpha.decode 4 bytes
  pure ({ marketCenterIdentifier, issueSymbol, securityClass, originalTradeControlNumber, originalTradePrice, originalNavPremiumDiscountAmount, originalTradeSize, originalSaleConditionModifier }, bytes)

@[simp] theorem encode_length (message : TradeCancelErrorForNextSharesMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, MarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeCancelErrorForNextSharesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelErrorForNextSharesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketCenterIdentifier.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCancelErrorForNextSharesMessage

/-- Trade Correction Message: 54 bytes -/
structure TradeCorrectionMessage where
  marketCenterIdentifier : MarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  originalTradeControlNumber : Alpha 10
  originalTradePrice : BitVec 32
  originalTradeSize : BitVec 32
  originalSaleConditionModifier : Alpha 4
  correctedTradeControlNumber : Alpha 10
  correctedTradePrice : BitVec 32
  correctedTradeSize : BitVec 32
  correctedSaleConditionModifier : Alpha 4
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  MarketCenterIdentifier.encode message.marketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.originalTradeControlNumber
    ++ (encodeUInt 4 message.originalTradePrice
    ++ (encodeUInt 4 message.originalTradeSize
    ++ (Alpha.encode message.originalSaleConditionModifier
    ++ (Alpha.encode message.correctedTradeControlNumber
    ++ (encodeUInt 4 message.correctedTradePrice
    ++ (encodeUInt 4 message.correctedTradeSize
    ++ (Alpha.encode message.correctedSaleConditionModifier))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (marketCenterIdentifier, bytes) ← MarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (originalTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (originalTradePrice, bytes) ← decodeUInt 4 bytes
  let (originalTradeSize, bytes) ← decodeUInt 4 bytes
  let (originalSaleConditionModifier, bytes) ← Alpha.decode 4 bytes
  let (correctedTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (correctedTradePrice, bytes) ← decodeUInt 4 bytes
  let (correctedTradeSize, bytes) ← decodeUInt 4 bytes
  let (correctedSaleConditionModifier, bytes) ← Alpha.decode 4 bytes
  pure ({ marketCenterIdentifier, issueSymbol, securityClass, originalTradeControlNumber, originalTradePrice, originalTradeSize, originalSaleConditionModifier, correctedTradeControlNumber, correctedTradePrice, correctedTradeSize, correctedSaleConditionModifier }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, MarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketCenterIdentifier.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCorrectionMessage

/-- Trade Correction For Next Shares Message: 62 bytes -/
structure TradeCorrectionForNextSharesMessage where
  marketCenterIdentifier : MarketCenterIdentifier
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  originalTradeControlNumber : Alpha 10
  originalTradePrice : BitVec 32
  originalNavPremiumDiscountAmount : BitVec 32
  originalTradeSize : BitVec 32
  originalSaleConditionModifier : Alpha 4
  correctedTradeControlNumber : Alpha 10
  correctedTradePrice : BitVec 32
  correctedNavPremiumDiscountAmount : BitVec 32
  correctedTradeSize : BitVec 32
  correctedSaleConditionModifier : Alpha 4
  deriving DecidableEq, Repr

namespace TradeCorrectionForNextSharesMessage

def encode (message : TradeCorrectionForNextSharesMessage) : List UInt8 :=
  MarketCenterIdentifier.encode message.marketCenterIdentifier
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (Alpha.encode message.originalTradeControlNumber
    ++ (encodeUInt 4 message.originalTradePrice
    ++ (encodeUInt 4 message.originalNavPremiumDiscountAmount
    ++ (encodeUInt 4 message.originalTradeSize
    ++ (Alpha.encode message.originalSaleConditionModifier
    ++ (Alpha.encode message.correctedTradeControlNumber
    ++ (encodeUInt 4 message.correctedTradePrice
    ++ (encodeUInt 4 message.correctedNavPremiumDiscountAmount
    ++ (encodeUInt 4 message.correctedTradeSize
    ++ (Alpha.encode message.correctedSaleConditionModifier))))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionForNextSharesMessage × List UInt8) := do
  let (marketCenterIdentifier, bytes) ← MarketCenterIdentifier.decode bytes
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (originalTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (originalTradePrice, bytes) ← decodeUInt 4 bytes
  let (originalNavPremiumDiscountAmount, bytes) ← decodeUInt 4 bytes
  let (originalTradeSize, bytes) ← decodeUInt 4 bytes
  let (originalSaleConditionModifier, bytes) ← Alpha.decode 4 bytes
  let (correctedTradeControlNumber, bytes) ← Alpha.decode 10 bytes
  let (correctedTradePrice, bytes) ← decodeUInt 4 bytes
  let (correctedNavPremiumDiscountAmount, bytes) ← decodeUInt 4 bytes
  let (correctedTradeSize, bytes) ← decodeUInt 4 bytes
  let (correctedSaleConditionModifier, bytes) ← Alpha.decode 4 bytes
  pure ({ marketCenterIdentifier, issueSymbol, securityClass, originalTradeControlNumber, originalTradePrice, originalNavPremiumDiscountAmount, originalTradeSize, originalSaleConditionModifier, correctedTradeControlNumber, correctedTradePrice, correctedNavPremiumDiscountAmount, correctedTradeSize, correctedSaleConditionModifier }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionForNextSharesMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, MarketCenterIdentifier.encode_length, Alpha.encode_length, SecurityClass.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeCorrectionForNextSharesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionForNextSharesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketCenterIdentifier.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCorrectionForNextSharesMessage

/-- Trading Action Message: 14 bytes -/
structure TradingActionMessage where
  issueSymbol : Alpha 8
  securityClass : SecurityClass
  currentTradingState : CurrentTradingState
  tradingActionReason : Alpha 4
  deriving DecidableEq, Repr

namespace TradingActionMessage

def encode (message : TradingActionMessage) : List UInt8 :=
  Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (CurrentTradingState.encode message.currentTradingState
    ++ (Alpha.encode message.tradingActionReason)))

def decode (bytes : List UInt8) : Option (TradingActionMessage × List UInt8) := do
  let (issueSymbol, bytes) ← Alpha.decode 8 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  let (tradingActionReason, bytes) ← Alpha.decode 4 bytes
  pure ({ issueSymbol, securityClass, currentTradingState, tradingActionReason }, bytes)

@[simp] theorem encode_length (message : TradingActionMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SecurityClass.encode_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : TradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CurrentTradingState.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradingActionMessage

/-- Reg Sho Short Sale Price Test Restricted Indicator Message: 9 bytes -/
structure RegShoShortSalePriceTestRestrictedIndicatorMessage where
  stock : Alpha 8
  regShoAction : RegShoAction
  deriving DecidableEq, Repr

namespace RegShoShortSalePriceTestRestrictedIndicatorMessage

def encode (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : List UInt8 :=
  Alpha.encode message.stock
    ++ (RegShoAction.encode message.regShoAction)

def decode (bytes : List UInt8) : Option (RegShoShortSalePriceTestRestrictedIndicatorMessage × List UInt8) := do
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (regShoAction, bytes) ← RegShoAction.decode bytes
  pure ({ stock, regShoAction }, bytes)

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

/-- Stock Directory Message: 28 bytes -/
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
    ++ (InverseIndicator.encode message.inverseIndicator)))))))))))))

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
  pure ({ stock, marketCategory, financialStatusIndicator, roundLotSize, roundLotsOnly := roundLotsOnly_, issueClassification, issueSubType, authenticity, shortSaleThresholdIndicator, ipoFlag, luldReferencePriceTier, etpFlag, etpLeverageFactor, inverseIndicator }, bytes)

@[simp] theorem encode_length (message : StockDirectoryMessage) : (encode message).length = 28 := by
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
  rw [InverseIndicator.decode_encode, some_bind]
  rfl

end StockDirectoryMessage

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

/-- Mwcb Breach Message: 1 bytes -/
structure MwcbBreachMessage where
  breachedLevel : BreachedLevel
  deriving DecidableEq, Repr

namespace MwcbBreachMessage

def encode (message : MwcbBreachMessage) : List UInt8 :=
  BreachedLevel.encode message.breachedLevel

def decode (bytes : List UInt8) : Option (MwcbBreachMessage × List UInt8) := do
  let (breachedLevel, bytes) ← BreachedLevel.decode bytes
  pure ({ breachedLevel }, bytes)

@[simp] theorem encode_length (message : MwcbBreachMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [BreachedLevel.encode_length]

theorem encode_length_pos (message : MwcbBreachMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MwcbBreachMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [BreachedLevel.decode_encode, some_bind]
  rfl

end MwcbBreachMessage

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
  | nextSharesTradeReportMessage (message : NextSharesTradeReportMessage) -- "M" 0x4D
  | tradeCancelErrorMessage (message : TradeCancelErrorMessage) -- "X" 0x58
  | tradeCancelErrorForNextSharesMessage (message : TradeCancelErrorForNextSharesMessage) -- "O" 0x4F
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "C" 0x43
  | tradeCorrectionForNextSharesMessage (message : TradeCorrectionForNextSharesMessage) -- "Z" 0x5A
  | tradingActionMessage (message : TradingActionMessage) -- "H" 0x48
  | regShoShortSalePriceTestRestrictedIndicatorMessage (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) -- "Y" 0x59
  | stockDirectoryMessage (message : StockDirectoryMessage) -- "R" 0x52
  | mwcbDeclineLevelMessage (message : MwcbDeclineLevelMessage) -- "V" 0x56
  | mwcbBreachMessage (message : MwcbBreachMessage) -- "W" 0x57
  | operationalHaltMessage (message : OperationalHaltMessage) -- "h" 0x68
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .tradeReportMessage _ => 84
  | .nextSharesTradeReportMessage _ => 77
  | .tradeCancelErrorMessage _ => 88
  | .tradeCancelErrorForNextSharesMessage _ => 79
  | .tradeCorrectionMessage _ => 67
  | .tradeCorrectionForNextSharesMessage _ => 90
  | .tradingActionMessage _ => 72
  | .regShoShortSalePriceTestRestrictedIndicatorMessage _ => 89
  | .stockDirectoryMessage _ => 82
  | .mwcbDeclineLevelMessage _ => 86
  | .mwcbBreachMessage _ => 87
  | .operationalHaltMessage _ => 104

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .tradeReportMessage message => TradeReportMessage.encode message
  | .nextSharesTradeReportMessage message => NextSharesTradeReportMessage.encode message
  | .tradeCancelErrorMessage message => TradeCancelErrorMessage.encode message
  | .tradeCancelErrorForNextSharesMessage message => TradeCancelErrorForNextSharesMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message
  | .tradeCorrectionForNextSharesMessage message => TradeCorrectionForNextSharesMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .regShoShortSalePriceTestRestrictedIndicatorMessage message => RegShoShortSalePriceTestRestrictedIndicatorMessage.encode message
  | .stockDirectoryMessage message => StockDirectoryMessage.encode message
  | .mwcbDeclineLevelMessage message => MwcbDeclineLevelMessage.encode message
  | .mwcbBreachMessage message => MwcbBreachMessage.encode message
  | .operationalHaltMessage message => OperationalHaltMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 62 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [encode, TradeReportMessage.encode_length]
    omega
  | nextSharesTradeReportMessage inner =>
    simp only [encode, NextSharesTradeReportMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [encode, TradeCancelErrorMessage.encode_length]
    omega
  | tradeCancelErrorForNextSharesMessage inner =>
    simp only [encode, TradeCancelErrorForNextSharesMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega
  | tradeCorrectionForNextSharesMessage inner =>
    simp only [encode, TradeCorrectionForNextSharesMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [encode, TradingActionMessage.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [encode, RegShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [encode, StockDirectoryMessage.encode_length]
    omega
  | mwcbDeclineLevelMessage inner =>
    simp only [encode, MwcbDeclineLevelMessage.encode_length]
    omega
  | mwcbBreachMessage inner =>
    simp only [encode, MwcbBreachMessage.encode_length]
    omega
  | operationalHaltMessage inner =>
    simp only [encode, OperationalHaltMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 84 then (TradeReportMessage.decode bytes).map fun (message, rest) => (.tradeReportMessage message, rest)
  else if tag = 77 then (NextSharesTradeReportMessage.decode bytes).map fun (message, rest) => (.nextSharesTradeReportMessage message, rest)
  else if tag = 88 then (TradeCancelErrorMessage.decode bytes).map fun (message, rest) => (.tradeCancelErrorMessage message, rest)
  else if tag = 79 then (TradeCancelErrorForNextSharesMessage.decode bytes).map fun (message, rest) => (.tradeCancelErrorForNextSharesMessage message, rest)
  else if tag = 67 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else if tag = 90 then (TradeCorrectionForNextSharesMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionForNextSharesMessage message, rest)
  else if tag = 72 then (TradingActionMessage.decode bytes).map fun (message, rest) => (.tradingActionMessage message, rest)
  else if tag = 89 then (RegShoShortSalePriceTestRestrictedIndicatorMessage.decode bytes).map fun (message, rest) => (.regShoShortSalePriceTestRestrictedIndicatorMessage message, rest)
  else if tag = 82 then (StockDirectoryMessage.decode bytes).map fun (message, rest) => (.stockDirectoryMessage message, rest)
  else if tag = 86 then (MwcbDeclineLevelMessage.decode bytes).map fun (message, rest) => (.mwcbDeclineLevelMessage message, rest)
  else if tag = 87 then (MwcbBreachMessage.decode bytes).map fun (message, rest) => (.mwcbBreachMessage message, rest)
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
  | nextSharesTradeReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, NextSharesTradeReportMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradeCancelErrorMessage.encode_length]
    omega
  | tradeCancelErrorForNextSharesMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradeCancelErrorForNextSharesMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradeCorrectionMessage.encode_length]
    omega
  | tradeCorrectionForNextSharesMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradeCorrectionForNextSharesMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradingActionMessage.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RegShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StockDirectoryMessage.encode_length]
    omega
  | mwcbDeclineLevelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MwcbDeclineLevelMessage.encode_length]
    omega
  | mwcbBreachMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MwcbBreachMessage.encode_length]
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

end Omi.NasdaqPsxequitiesLastsaleItchV212018
