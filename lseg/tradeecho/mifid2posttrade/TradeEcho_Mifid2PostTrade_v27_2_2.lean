import Wire

/-!
# London Stock Exchange MiFID II Post Trade v27.2.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Allowed Book Types is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LsegTradeechoMifid2posttradeGtpV2722

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x54, 0x50, 0x43]

inductive EventCode where
  | startOfDay -- Start Of Day
  | startOfOpen -- Start Of Open
  | startOfPreClose -- Start Of Pre Close
  | endOfDay -- End Of Day
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfDay => 0x4F
  | .startOfOpen => 0x54
  | .startOfPreClose => 0x50
  | .endOfDay => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfDay
  else if byte = 0x54 then .startOfOpen
  else if byte = 0x50 then .startOfPreClose
  else .endOfDay

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfDay => decide
  | startOfOpen => decide
  | startOfPreClose => decide
  | endOfDay => decide
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

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x50]

inductive TradingStatus where
  | inactive -- Inactive
  | suspended -- Suspended
  | active -- Active
  | regulatoryHalt -- Regulatory Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .inactive => 0x31
  | .suspended => 0x32
  | .active => 0x33
  | .regulatoryHalt => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x31 then .inactive
  else if byte = 0x32 then .suspended
  else if byte = 0x33 then .active
  else .regulatoryHalt

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | inactive => decide
  | suspended => decide
  | active => decide
  | regulatoryHalt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingStatus

/-- Transaction To Be Cleared: one byte code -/
def TransactionToBeCleared.codes : List UInt8 :=
  [0x30, 0x31]

inductive TransactionToBeCleared where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionToBeCleared.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionToBeCleared

def toByte : TransactionToBeCleared → UInt8
  | .no => 0x30
  | .yes => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionToBeCleared :=
  if byte = 0x30 then .no
  else .yes

def ofByte (byte : UInt8) : TransactionToBeCleared :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionToBeCleared) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionToBeCleared) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionToBeCleared × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionToBeCleared) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TransactionToBeCleared) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionToBeCleared

/-- Market Mechanism: one byte code -/
def MarketMechanism.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]

inductive MarketMechanism where
  | centralLimitOrderBook -- Central Limit Order Book
  | quoteDrivenMarket -- Quote Driven Market
  | darkOrderBook -- Dark Order Book
  | offBook -- Off Book
  | periodicAuction -- Periodic Auction
  | requestForQuotes -- Request For Quotes
  | anyOtherIncludingHybrid -- Any Other Including Hybrid
  | hybridMarket -- Hybrid Market
  | otherMarket -- Other Market
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketMechanism.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketMechanism

def toByte : MarketMechanism → UInt8
  | .centralLimitOrderBook => 0x31
  | .quoteDrivenMarket => 0x32
  | .darkOrderBook => 0x33
  | .offBook => 0x34
  | .periodicAuction => 0x35
  | .requestForQuotes => 0x36
  | .anyOtherIncludingHybrid => 0x37
  | .hybridMarket => 0x38
  | .otherMarket => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketMechanism :=
  if byte = 0x31 then .centralLimitOrderBook
  else if byte = 0x32 then .quoteDrivenMarket
  else if byte = 0x33 then .darkOrderBook
  else if byte = 0x34 then .offBook
  else if byte = 0x35 then .periodicAuction
  else if byte = 0x36 then .requestForQuotes
  else if byte = 0x37 then .anyOtherIncludingHybrid
  else if byte = 0x38 then .hybridMarket
  else .otherMarket

def ofByte (byte : UInt8) : MarketMechanism :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketMechanism) : ofByte value.toByte = value := by
  cases value with
  | centralLimitOrderBook => decide
  | quoteDrivenMarket => decide
  | darkOrderBook => decide
  | offBook => decide
  | periodicAuction => decide
  | requestForQuotes => decide
  | anyOtherIncludingHybrid => decide
  | hybridMarket => decide
  | otherMarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketMechanism) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketMechanism × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketMechanism) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketMechanism) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketMechanism

/-- Trading Mode: one byte code -/
def TradingMode.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x4F, 0x4B, 0x49, 0x55]

inductive TradingMode where
  | undefinedAuction -- Undefined Auction
  | continuousTrading -- Continuous Trading
  | atMarketCloseTrading -- At Market Close Trading
  | outOfMainSessionTrading -- Out Of Main Session Trading
  | tradeReportingOnExchange -- Trade Reporting On Exchange
  | tradeReportingOffExchange -- Trade Reporting Off Exchange
  | tradeReportingSystemicInternaliser -- Trade Reporting Systemic Internaliser
  | scheduledOpeningAuction -- Scheduled Opening Auction
  | scheduledClosingAuction -- Scheduled Closing Auction
  | scheduledIntradayAuction -- Scheduled Intraday Auction
  | unscheduledAuction -- Unscheduled Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingMode

def toByte : TradingMode → UInt8
  | .undefinedAuction => 0x31
  | .continuousTrading => 0x32
  | .atMarketCloseTrading => 0x33
  | .outOfMainSessionTrading => 0x34
  | .tradeReportingOnExchange => 0x35
  | .tradeReportingOffExchange => 0x36
  | .tradeReportingSystemicInternaliser => 0x37
  | .scheduledOpeningAuction => 0x4F
  | .scheduledClosingAuction => 0x4B
  | .scheduledIntradayAuction => 0x49
  | .unscheduledAuction => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingMode :=
  if byte = 0x31 then .undefinedAuction
  else if byte = 0x32 then .continuousTrading
  else if byte = 0x33 then .atMarketCloseTrading
  else if byte = 0x34 then .outOfMainSessionTrading
  else if byte = 0x35 then .tradeReportingOnExchange
  else if byte = 0x36 then .tradeReportingOffExchange
  else if byte = 0x37 then .tradeReportingSystemicInternaliser
  else if byte = 0x4F then .scheduledOpeningAuction
  else if byte = 0x4B then .scheduledClosingAuction
  else if byte = 0x49 then .scheduledIntradayAuction
  else .unscheduledAuction

def ofByte (byte : UInt8) : TradingMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingMode) : ofByte value.toByte = value := by
  cases value with
  | undefinedAuction => decide
  | continuousTrading => decide
  | atMarketCloseTrading => decide
  | outOfMainSessionTrading => decide
  | tradeReportingOnExchange => decide
  | tradeReportingOffExchange => decide
  | tradeReportingSystemicInternaliser => decide
  | scheduledOpeningAuction => decide
  | scheduledClosingAuction => decide
  | scheduledIntradayAuction => decide
  | unscheduledAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingMode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingMode

/-- Transaction Category: one byte code -/
def TransactionCategory.codes : List UInt8 :=
  [0x52, 0x5A, 0x59, 0x47, 0x48, 0x2D]

inductive TransactionCategory where
  | tradeThatHasReceivedPriceImprovement -- Trade That Has Received Price Improvement
  | packageTradeExcludingExchangeForPhysicals -- Package Trade Excluding Exchange For Physicals
  | exchangeForPhysicalsTrade -- Exchange For Physicals Trade
  | rfmdGiveUpTrade -- Rfmd Give Up Trade
  | rfmdGiveUpTradeAndExchangeForPhysicalsTrade -- Rfmd Give Up Trade And Exchange For Physicals Trade
  | noneApply -- None Apply
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionCategory

def toByte : TransactionCategory → UInt8
  | .tradeThatHasReceivedPriceImprovement => 0x52
  | .packageTradeExcludingExchangeForPhysicals => 0x5A
  | .exchangeForPhysicalsTrade => 0x59
  | .rfmdGiveUpTrade => 0x47
  | .rfmdGiveUpTradeAndExchangeForPhysicalsTrade => 0x48
  | .noneApply => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionCategory :=
  if byte = 0x52 then .tradeThatHasReceivedPriceImprovement
  else if byte = 0x5A then .packageTradeExcludingExchangeForPhysicals
  else if byte = 0x59 then .exchangeForPhysicalsTrade
  else if byte = 0x47 then .rfmdGiveUpTrade
  else if byte = 0x48 then .rfmdGiveUpTradeAndExchangeForPhysicalsTrade
  else .noneApply

def ofByte (byte : UInt8) : TransactionCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionCategory) : ofByte value.toByte = value := by
  cases value with
  | tradeThatHasReceivedPriceImprovement => decide
  | packageTradeExcludingExchangeForPhysicals => decide
  | exchangeForPhysicalsTrade => decide
  | rfmdGiveUpTrade => decide
  | rfmdGiveUpTradeAndExchangeForPhysicalsTrade => decide
  | noneApply => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TransactionCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionCategory

/-- Negotiation Indicator: one byte code -/
def NegotiationIndicator.codes : List UInt8 :=
  [0x4E, 0x31, 0x32, 0x33, 0x37, 0x38, 0x2D]

inductive NegotiationIndicator where
  | negotiationTrade -- Negotiation Trade
  | negotiatedTradeInLiquidFinancialInstruments -- Negotiated Trade In Liquid Financial Instruments
  | negotiatedTradeInIlliquidFinancialInstruments -- Negotiated Trade In Illiquid Financial Instruments
  | negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPrice -- Negotiated Trade Subject To Conditions Other Than The Current Market Price
  | negotiatedTradeLargerThanLisBroughtOntoAVenue -- Negotiated Trade Larger Than Lis Brought Onto A Venue
  | negotiatedTradeWithPreTradeTransparencyWaiver -- Negotiated Trade With Pre Trade Transparency Waiver
  | notANegotiatedTrade -- Not A Negotiated Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ NegotiationIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NegotiationIndicator

def toByte : NegotiationIndicator → UInt8
  | .negotiationTrade => 0x4E
  | .negotiatedTradeInLiquidFinancialInstruments => 0x31
  | .negotiatedTradeInIlliquidFinancialInstruments => 0x32
  | .negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPrice => 0x33
  | .negotiatedTradeLargerThanLisBroughtOntoAVenue => 0x37
  | .negotiatedTradeWithPreTradeTransparencyWaiver => 0x38
  | .notANegotiatedTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NegotiationIndicator :=
  if byte = 0x4E then .negotiationTrade
  else if byte = 0x31 then .negotiatedTradeInLiquidFinancialInstruments
  else if byte = 0x32 then .negotiatedTradeInIlliquidFinancialInstruments
  else if byte = 0x33 then .negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPrice
  else if byte = 0x37 then .negotiatedTradeLargerThanLisBroughtOntoAVenue
  else if byte = 0x38 then .negotiatedTradeWithPreTradeTransparencyWaiver
  else .notANegotiatedTrade

def ofByte (byte : UInt8) : NegotiationIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NegotiationIndicator) : ofByte value.toByte = value := by
  cases value with
  | negotiationTrade => decide
  | negotiatedTradeInLiquidFinancialInstruments => decide
  | negotiatedTradeInIlliquidFinancialInstruments => decide
  | negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPrice => decide
  | negotiatedTradeLargerThanLisBroughtOntoAVenue => decide
  | negotiatedTradeWithPreTradeTransparencyWaiver => decide
  | notANegotiatedTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NegotiationIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NegotiationIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NegotiationIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NegotiationIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NegotiationIndicator

/-- Agency Cross Indicator: one byte code -/
def AgencyCrossIndicator.codes : List UInt8 :=
  [0x58, 0x4D, 0x2D]

inductive AgencyCrossIndicator where
  | agencyCrossTrade -- Agency Cross Trade
  | matchedPrincipalTrade -- Matched Principal Trade
  | noAgencyCrossTrade -- No Agency Cross Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ AgencyCrossIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AgencyCrossIndicator

def toByte : AgencyCrossIndicator → UInt8
  | .agencyCrossTrade => 0x58
  | .matchedPrincipalTrade => 0x4D
  | .noAgencyCrossTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AgencyCrossIndicator :=
  if byte = 0x58 then .agencyCrossTrade
  else if byte = 0x4D then .matchedPrincipalTrade
  else .noAgencyCrossTrade

def ofByte (byte : UInt8) : AgencyCrossIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AgencyCrossIndicator) : ofByte value.toByte = value := by
  cases value with
  | agencyCrossTrade => decide
  | matchedPrincipalTrade => decide
  | noAgencyCrossTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AgencyCrossIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AgencyCrossIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AgencyCrossIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AgencyCrossIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AgencyCrossIndicator

/-- Modification Indicator: one byte code -/
def ModificationIndicator.codes : List UInt8 :=
  [0x43, 0x41, 0x2D]

inductive ModificationIndicator where
  | tradeCancellation -- Trade Cancellation
  | tradeAmendment -- Trade Amendment
  | newTrade -- New Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ ModificationIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ModificationIndicator

def toByte : ModificationIndicator → UInt8
  | .tradeCancellation => 0x43
  | .tradeAmendment => 0x41
  | .newTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ModificationIndicator :=
  if byte = 0x43 then .tradeCancellation
  else if byte = 0x41 then .tradeAmendment
  else .newTrade

def ofByte (byte : UInt8) : ModificationIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ModificationIndicator) : ofByte value.toByte = value := by
  cases value with
  | tradeCancellation => decide
  | tradeAmendment => decide
  | newTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ModificationIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ModificationIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ModificationIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ModificationIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ModificationIndicator

/-- Reference Price Indicator: one byte code -/
def ReferencePriceIndicator.codes : List UInt8 :=
  [0x42, 0x53, 0x4F, 0x4E, 0x4D, 0x59, 0x43, 0x50, 0x31, 0x32, 0x36, 0x2D]

inductive ReferencePriceIndicator where
  | benchmarkTrade -- Benchmark Trade
  | referencePriceTrade -- Reference Price Trade
  | benchmarkTradeAndPortfolioTransactionAndContingentTransaction -- Benchmark Trade And Portfolio Transaction And Contingent Transaction
  | portfolioTransactionAndContingentTransaction -- Portfolio Transaction And Contingent Transaction
  | benchmarkTradeAndContingentTransaction -- Benchmark Trade And Contingent Transaction
  | benchmarkTradeAndPortfolioTransaction -- Benchmark Trade And Portfolio Transaction
  | contingentTransaction -- Contingent Transaction
  | portfolioTransaction -- Portfolio Transaction
  | marketClosingPrice -- Market Closing Price
  | marketClosingPriceAndPortfolioTransaction -- Market Closing Price And Portfolio Transaction
  | referencePriceTradeAndMarketClosingPrice -- Reference Price Trade And Market Closing Price
  | notAReferencePriceTrade -- Not A Reference Price Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ ReferencePriceIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReferencePriceIndicator

def toByte : ReferencePriceIndicator → UInt8
  | .benchmarkTrade => 0x42
  | .referencePriceTrade => 0x53
  | .benchmarkTradeAndPortfolioTransactionAndContingentTransaction => 0x4F
  | .portfolioTransactionAndContingentTransaction => 0x4E
  | .benchmarkTradeAndContingentTransaction => 0x4D
  | .benchmarkTradeAndPortfolioTransaction => 0x59
  | .contingentTransaction => 0x43
  | .portfolioTransaction => 0x50
  | .marketClosingPrice => 0x31
  | .marketClosingPriceAndPortfolioTransaction => 0x32
  | .referencePriceTradeAndMarketClosingPrice => 0x36
  | .notAReferencePriceTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReferencePriceIndicator :=
  if byte = 0x42 then .benchmarkTrade
  else if byte = 0x53 then .referencePriceTrade
  else if byte = 0x4F then .benchmarkTradeAndPortfolioTransactionAndContingentTransaction
  else if byte = 0x4E then .portfolioTransactionAndContingentTransaction
  else if byte = 0x4D then .benchmarkTradeAndContingentTransaction
  else if byte = 0x59 then .benchmarkTradeAndPortfolioTransaction
  else if byte = 0x43 then .contingentTransaction
  else if byte = 0x50 then .portfolioTransaction
  else if byte = 0x31 then .marketClosingPrice
  else if byte = 0x32 then .marketClosingPriceAndPortfolioTransaction
  else if byte = 0x36 then .referencePriceTradeAndMarketClosingPrice
  else .notAReferencePriceTrade

def ofByte (byte : UInt8) : ReferencePriceIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReferencePriceIndicator) : ofByte value.toByte = value := by
  cases value with
  | benchmarkTrade => decide
  | referencePriceTrade => decide
  | benchmarkTradeAndPortfolioTransactionAndContingentTransaction => decide
  | portfolioTransactionAndContingentTransaction => decide
  | benchmarkTradeAndContingentTransaction => decide
  | benchmarkTradeAndPortfolioTransaction => decide
  | contingentTransaction => decide
  | portfolioTransaction => decide
  | marketClosingPrice => decide
  | marketClosingPriceAndPortfolioTransaction => decide
  | referencePriceTradeAndMarketClosingPrice => decide
  | notAReferencePriceTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReferencePriceIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReferencePriceIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReferencePriceIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReferencePriceIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReferencePriceIndicator

/-- Special Dividend Indicator: one byte code -/
def SpecialDividendIndicator.codes : List UInt8 :=
  [0x45, 0x2D]

inductive SpecialDividendIndicator where
  | specialDividendTrade -- Special Dividend Trade
  | noSpecialDividendTrade -- No Special Dividend Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ SpecialDividendIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SpecialDividendIndicator

def toByte : SpecialDividendIndicator → UInt8
  | .specialDividendTrade => 0x45
  | .noSpecialDividendTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SpecialDividendIndicator :=
  if byte = 0x45 then .specialDividendTrade
  else .noSpecialDividendTrade

def ofByte (byte : UInt8) : SpecialDividendIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SpecialDividendIndicator) : ofByte value.toByte = value := by
  cases value with
  | specialDividendTrade => decide
  | noSpecialDividendTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SpecialDividendIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SpecialDividendIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SpecialDividendIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SpecialDividendIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SpecialDividendIndicator

/-- Off Book Automated Indicator: one byte code -/
def OffBookAutomatedIndicator.codes : List UInt8 :=
  [0x4D, 0x51, 0x2D]

inductive OffBookAutomatedIndicator where
  | offBookNonAutomated -- Off Book Non Automated
  | offBookAutomated -- Off Book Automated
  | unspecifiedOrDoesNotApply -- Unspecified Or Does Not Apply
  | unlisted (byte : { byte : UInt8 // byte ∉ OffBookAutomatedIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OffBookAutomatedIndicator

def toByte : OffBookAutomatedIndicator → UInt8
  | .offBookNonAutomated => 0x4D
  | .offBookAutomated => 0x51
  | .unspecifiedOrDoesNotApply => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OffBookAutomatedIndicator :=
  if byte = 0x4D then .offBookNonAutomated
  else if byte = 0x51 then .offBookAutomated
  else .unspecifiedOrDoesNotApply

def ofByte (byte : UInt8) : OffBookAutomatedIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OffBookAutomatedIndicator) : ofByte value.toByte = value := by
  cases value with
  | offBookNonAutomated => decide
  | offBookAutomated => decide
  | unspecifiedOrDoesNotApply => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OffBookAutomatedIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OffBookAutomatedIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OffBookAutomatedIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OffBookAutomatedIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OffBookAutomatedIndicator

/-- Price Formation Indicator: one byte code -/
def PriceFormationIndicator.codes : List UInt8 :=
  [0x50, 0x54, 0x4A, 0x4E, 0x5A]

inductive PriceFormationIndicator where
  | plainVanillaTrade -- Plain Vanilla Trade
  | nonPriceFormingTrade -- Non Price Forming Trade
  | tradeNotContributingToPriceDiscovery -- Trade Not Contributing To Price Discovery
  | pendingPrice -- Pending Price
  | priceIsNotApplicable -- Price Is Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceFormationIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceFormationIndicator

def toByte : PriceFormationIndicator → UInt8
  | .plainVanillaTrade => 0x50
  | .nonPriceFormingTrade => 0x54
  | .tradeNotContributingToPriceDiscovery => 0x4A
  | .pendingPrice => 0x4E
  | .priceIsNotApplicable => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceFormationIndicator :=
  if byte = 0x50 then .plainVanillaTrade
  else if byte = 0x54 then .nonPriceFormingTrade
  else if byte = 0x4A then .tradeNotContributingToPriceDiscovery
  else if byte = 0x4E then .pendingPrice
  else .priceIsNotApplicable

def ofByte (byte : UInt8) : PriceFormationIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceFormationIndicator) : ofByte value.toByte = value := by
  cases value with
  | plainVanillaTrade => decide
  | nonPriceFormingTrade => decide
  | tradeNotContributingToPriceDiscovery => decide
  | pendingPrice => decide
  | priceIsNotApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceFormationIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceFormationIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceFormationIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceFormationIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceFormationIndicator

/-- Algorithmic Indicator: one byte code -/
def AlgorithmicIndicator.codes : List UInt8 :=
  [0x48, 0x2D]

inductive AlgorithmicIndicator where
  | algorithmicTrade -- Algorithmic Trade
  | notAnAlgorithmicTrade -- Not An Algorithmic Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ AlgorithmicIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AlgorithmicIndicator

def toByte : AlgorithmicIndicator → UInt8
  | .algorithmicTrade => 0x48
  | .notAnAlgorithmicTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AlgorithmicIndicator :=
  if byte = 0x48 then .algorithmicTrade
  else .notAnAlgorithmicTrade

def ofByte (byte : UInt8) : AlgorithmicIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AlgorithmicIndicator) : ofByte value.toByte = value := by
  cases value with
  | algorithmicTrade => decide
  | notAnAlgorithmicTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AlgorithmicIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AlgorithmicIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AlgorithmicIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AlgorithmicIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AlgorithmicIndicator

/-- Post Trade Deferral Reason: one byte code -/
def PostTradeDeferralReason.codes : List UInt8 :=
  [0x32, 0x33, 0x34, 0x35, 0x36, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x2D]

inductive PostTradeDeferralReason where
  | nonImmediatePublicationDeferralForLargeInScale -- Non Immediate Publication Deferral For Large In Scale
  | nonImmediatePublicationDeferralForIlliquidInstrument -- Non Immediate Publication Deferral For Illiquid Instrument
  | nonImmediatePublicationDeferralForSizeSpecific -- Non Immediate Publication Deferral For Size Specific
  | nonImmediatePublicationDeferralsOfIlliquidInstrumentAndSizeSpecific -- Non Immediate Publication Deferrals Of Illiquid Instrument And Size Specific
  | nonImmediatePublicationDeferralsOfIlliquidInstrumentAndLargeInScale -- Non Immediate Publication Deferrals Of Illiquid Instrument And Large In Scale
  | nonImmediatePublicationDeferralForMediumSizeLiquidMarket -- Non Immediate Publication Deferral For Medium Size Liquid Market
  | nonImmediatePublicationDeferralForMediumSizeIlliquidMarket -- Non Immediate Publication Deferral For Medium Size Illiquid Market
  | nonImmediatePublicationDeferralForLargeSizeLiquidMarket -- Non Immediate Publication Deferral For Large Size Liquid Market
  | nonImmediatePublicationDeferralForLargeSizeIlliquidMarket -- Non Immediate Publication Deferral For Large Size Illiquid Market
  | nonImmediatePublicationDeferralForVeryLargeSizeLiquidMarket -- Non Immediate Publication Deferral For Very Large Size Liquid Market
  | nonImmediatePublicationDeferralForVeryLargeSizeIlliquidMarket -- Non Immediate Publication Deferral For Very Large Size Illiquid Market
  | nonImmediatePublicationDeferralForEtCsEtNsSfPsEmissionAllowances -- Non Immediate Publication Deferral For Et Cs Et Ns Sf Ps Emission Allowances
  | immediatePublication -- Immediate Publication
  | unlisted (byte : { byte : UInt8 // byte ∉ PostTradeDeferralReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PostTradeDeferralReason

def toByte : PostTradeDeferralReason → UInt8
  | .nonImmediatePublicationDeferralForLargeInScale => 0x32
  | .nonImmediatePublicationDeferralForIlliquidInstrument => 0x33
  | .nonImmediatePublicationDeferralForSizeSpecific => 0x34
  | .nonImmediatePublicationDeferralsOfIlliquidInstrumentAndSizeSpecific => 0x35
  | .nonImmediatePublicationDeferralsOfIlliquidInstrumentAndLargeInScale => 0x36
  | .nonImmediatePublicationDeferralForMediumSizeLiquidMarket => 0x41
  | .nonImmediatePublicationDeferralForMediumSizeIlliquidMarket => 0x42
  | .nonImmediatePublicationDeferralForLargeSizeLiquidMarket => 0x43
  | .nonImmediatePublicationDeferralForLargeSizeIlliquidMarket => 0x44
  | .nonImmediatePublicationDeferralForVeryLargeSizeLiquidMarket => 0x45
  | .nonImmediatePublicationDeferralForVeryLargeSizeIlliquidMarket => 0x46
  | .nonImmediatePublicationDeferralForEtCsEtNsSfPsEmissionAllowances => 0x47
  | .immediatePublication => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PostTradeDeferralReason :=
  if byte = 0x32 then .nonImmediatePublicationDeferralForLargeInScale
  else if byte = 0x33 then .nonImmediatePublicationDeferralForIlliquidInstrument
  else if byte = 0x34 then .nonImmediatePublicationDeferralForSizeSpecific
  else if byte = 0x35 then .nonImmediatePublicationDeferralsOfIlliquidInstrumentAndSizeSpecific
  else if byte = 0x36 then .nonImmediatePublicationDeferralsOfIlliquidInstrumentAndLargeInScale
  else if byte = 0x41 then .nonImmediatePublicationDeferralForMediumSizeLiquidMarket
  else if byte = 0x42 then .nonImmediatePublicationDeferralForMediumSizeIlliquidMarket
  else if byte = 0x43 then .nonImmediatePublicationDeferralForLargeSizeLiquidMarket
  else if byte = 0x44 then .nonImmediatePublicationDeferralForLargeSizeIlliquidMarket
  else if byte = 0x45 then .nonImmediatePublicationDeferralForVeryLargeSizeLiquidMarket
  else if byte = 0x46 then .nonImmediatePublicationDeferralForVeryLargeSizeIlliquidMarket
  else if byte = 0x47 then .nonImmediatePublicationDeferralForEtCsEtNsSfPsEmissionAllowances
  else .immediatePublication

def ofByte (byte : UInt8) : PostTradeDeferralReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PostTradeDeferralReason) : ofByte value.toByte = value := by
  cases value with
  | nonImmediatePublicationDeferralForLargeInScale => decide
  | nonImmediatePublicationDeferralForIlliquidInstrument => decide
  | nonImmediatePublicationDeferralForSizeSpecific => decide
  | nonImmediatePublicationDeferralsOfIlliquidInstrumentAndSizeSpecific => decide
  | nonImmediatePublicationDeferralsOfIlliquidInstrumentAndLargeInScale => decide
  | nonImmediatePublicationDeferralForMediumSizeLiquidMarket => decide
  | nonImmediatePublicationDeferralForMediumSizeIlliquidMarket => decide
  | nonImmediatePublicationDeferralForLargeSizeLiquidMarket => decide
  | nonImmediatePublicationDeferralForLargeSizeIlliquidMarket => decide
  | nonImmediatePublicationDeferralForVeryLargeSizeLiquidMarket => decide
  | nonImmediatePublicationDeferralForVeryLargeSizeIlliquidMarket => decide
  | nonImmediatePublicationDeferralForEtCsEtNsSfPsEmissionAllowances => decide
  | immediatePublication => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PostTradeDeferralReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PostTradeDeferralReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PostTradeDeferralReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PostTradeDeferralReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PostTradeDeferralReason

/-- Deferral Enrichment Type: one byte code -/
def DeferralEnrichmentType.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x56, 0x57, 0x4A, 0x4C, 0x4B, 0x4D, 0x2D]

inductive DeferralEnrichmentType where
  | limitedDetailsTrade -- Limited Details Trade
  | dailyAggregatedTrade -- Daily Aggregated Trade
  | volumeOmissionTrade -- Volume Omission Trade
  | fourWeeksAggregationTrade -- Four Weeks Aggregation Trade
  | indefiniteAggregationTrade -- Indefinite Aggregation Trade
  | volumeOmissionTradeEligibleForSubsequentEnrichmentInAggregatedForm -- Volume Omission Trade Eligible For Subsequent Enrichment In Aggregated Form
  | fullDetailsOfEarlierLimitedDetailsTrade -- Full Details Of Earlier Limited Details Trade
  | fullDetailsOfEarlierDailyAggregatedTrade -- Full Details Of Earlier Daily Aggregated Trade
  | fullDetailsOfEarlierVolumeOmissionTrade -- Full Details Of Earlier Volume Omission Trade
  | fullDetailsOfEarlierFourWeeksAggregationTrade -- Full Details Of Earlier Four Weeks Aggregation Trade
  | fullDetailsInAggregatedFormOfEarlierVolumeOmissionTrade -- Full Details In Aggregated Form Of Earlier Volume Omission Trade
  | volumeOmissionForSovereignBondsTrade -- Volume Omission For Sovereign Bonds Trade
  | fullDetailsOfEarlierVolumeOmissionSovereignBondTrade -- Full Details Of Earlier Volume Omission Sovereign Bond Trade
  | fourWeeksAggregationForSovereignBondsTrade -- Four Weeks Aggregation For Sovereign Bonds Trade
  | fullDetailsOfEarlierAggregatedSovereignBondTrade -- Full Details Of Earlier Aggregated Sovereign Bond Trade
  | notApplicableOrNoRelevantEnrichmentType -- Not Applicable Or No Relevant Enrichment Type
  | unlisted (byte : { byte : UInt8 // byte ∉ DeferralEnrichmentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeferralEnrichmentType

def toByte : DeferralEnrichmentType → UInt8
  | .limitedDetailsTrade => 0x31
  | .dailyAggregatedTrade => 0x32
  | .volumeOmissionTrade => 0x33
  | .fourWeeksAggregationTrade => 0x34
  | .indefiniteAggregationTrade => 0x35
  | .volumeOmissionTradeEligibleForSubsequentEnrichmentInAggregatedForm => 0x36
  | .fullDetailsOfEarlierLimitedDetailsTrade => 0x37
  | .fullDetailsOfEarlierDailyAggregatedTrade => 0x38
  | .fullDetailsOfEarlierVolumeOmissionTrade => 0x39
  | .fullDetailsOfEarlierFourWeeksAggregationTrade => 0x56
  | .fullDetailsInAggregatedFormOfEarlierVolumeOmissionTrade => 0x57
  | .volumeOmissionForSovereignBondsTrade => 0x4A
  | .fullDetailsOfEarlierVolumeOmissionSovereignBondTrade => 0x4C
  | .fourWeeksAggregationForSovereignBondsTrade => 0x4B
  | .fullDetailsOfEarlierAggregatedSovereignBondTrade => 0x4D
  | .notApplicableOrNoRelevantEnrichmentType => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeferralEnrichmentType :=
  if byte = 0x31 then .limitedDetailsTrade
  else if byte = 0x32 then .dailyAggregatedTrade
  else if byte = 0x33 then .volumeOmissionTrade
  else if byte = 0x34 then .fourWeeksAggregationTrade
  else if byte = 0x35 then .indefiniteAggregationTrade
  else if byte = 0x36 then .volumeOmissionTradeEligibleForSubsequentEnrichmentInAggregatedForm
  else if byte = 0x37 then .fullDetailsOfEarlierLimitedDetailsTrade
  else if byte = 0x38 then .fullDetailsOfEarlierDailyAggregatedTrade
  else if byte = 0x39 then .fullDetailsOfEarlierVolumeOmissionTrade
  else if byte = 0x56 then .fullDetailsOfEarlierFourWeeksAggregationTrade
  else if byte = 0x57 then .fullDetailsInAggregatedFormOfEarlierVolumeOmissionTrade
  else if byte = 0x4A then .volumeOmissionForSovereignBondsTrade
  else if byte = 0x4C then .fullDetailsOfEarlierVolumeOmissionSovereignBondTrade
  else if byte = 0x4B then .fourWeeksAggregationForSovereignBondsTrade
  else if byte = 0x4D then .fullDetailsOfEarlierAggregatedSovereignBondTrade
  else .notApplicableOrNoRelevantEnrichmentType

def ofByte (byte : UInt8) : DeferralEnrichmentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeferralEnrichmentType) : ofByte value.toByte = value := by
  cases value with
  | limitedDetailsTrade => decide
  | dailyAggregatedTrade => decide
  | volumeOmissionTrade => decide
  | fourWeeksAggregationTrade => decide
  | indefiniteAggregationTrade => decide
  | volumeOmissionTradeEligibleForSubsequentEnrichmentInAggregatedForm => decide
  | fullDetailsOfEarlierLimitedDetailsTrade => decide
  | fullDetailsOfEarlierDailyAggregatedTrade => decide
  | fullDetailsOfEarlierVolumeOmissionTrade => decide
  | fullDetailsOfEarlierFourWeeksAggregationTrade => decide
  | fullDetailsInAggregatedFormOfEarlierVolumeOmissionTrade => decide
  | volumeOmissionForSovereignBondsTrade => decide
  | fullDetailsOfEarlierVolumeOmissionSovereignBondTrade => decide
  | fourWeeksAggregationForSovereignBondsTrade => decide
  | fullDetailsOfEarlierAggregatedSovereignBondTrade => decide
  | notApplicableOrNoRelevantEnrichmentType => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeferralEnrichmentType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeferralEnrichmentType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeferralEnrichmentType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DeferralEnrichmentType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeferralEnrichmentType

/-- Duplicative Indicator: one byte code -/
def DuplicativeIndicator.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x2D]

inductive DuplicativeIndicator where
  | duplicativeTradeReport -- Duplicative Trade Report
  | intraGroupTrade -- Intra Group Trade
  | duplicativeTradeReportAndIntraGroupTrade -- Duplicative Trade Report And Intra Group Trade
  | crossBorderDuplicativeTradeReport -- Cross Border Duplicative Trade Report
  | duplicativeTradeReportAndCrossBorderDuplicativeTradeReport -- Duplicative Trade Report And Cross Border Duplicative Trade Report
  | duplicativeTradeReportAndIntraGroupTradeAndCrossBorderDuplicativeTradeReport -- Duplicative Trade Report And Intra Group Trade And Cross Border Duplicative Trade Report
  | intraGroupTradeAndCrossBorderDuplicativeTradeReport -- Intra Group Trade And Cross Border Duplicative Trade Report
  | uniqueTradeReport -- Unique Trade Report
  | unlisted (byte : { byte : UInt8 // byte ∉ DuplicativeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DuplicativeIndicator

def toByte : DuplicativeIndicator → UInt8
  | .duplicativeTradeReport => 0x31
  | .intraGroupTrade => 0x32
  | .duplicativeTradeReportAndIntraGroupTrade => 0x33
  | .crossBorderDuplicativeTradeReport => 0x34
  | .duplicativeTradeReportAndCrossBorderDuplicativeTradeReport => 0x35
  | .duplicativeTradeReportAndIntraGroupTradeAndCrossBorderDuplicativeTradeReport => 0x36
  | .intraGroupTradeAndCrossBorderDuplicativeTradeReport => 0x37
  | .uniqueTradeReport => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DuplicativeIndicator :=
  if byte = 0x31 then .duplicativeTradeReport
  else if byte = 0x32 then .intraGroupTrade
  else if byte = 0x33 then .duplicativeTradeReportAndIntraGroupTrade
  else if byte = 0x34 then .crossBorderDuplicativeTradeReport
  else if byte = 0x35 then .duplicativeTradeReportAndCrossBorderDuplicativeTradeReport
  else if byte = 0x36 then .duplicativeTradeReportAndIntraGroupTradeAndCrossBorderDuplicativeTradeReport
  else if byte = 0x37 then .intraGroupTradeAndCrossBorderDuplicativeTradeReport
  else .uniqueTradeReport

def ofByte (byte : UInt8) : DuplicativeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DuplicativeIndicator) : ofByte value.toByte = value := by
  cases value with
  | duplicativeTradeReport => decide
  | intraGroupTrade => decide
  | duplicativeTradeReportAndIntraGroupTrade => decide
  | crossBorderDuplicativeTradeReport => decide
  | duplicativeTradeReportAndCrossBorderDuplicativeTradeReport => decide
  | duplicativeTradeReportAndIntraGroupTradeAndCrossBorderDuplicativeTradeReport => decide
  | intraGroupTradeAndCrossBorderDuplicativeTradeReport => decide
  | uniqueTradeReport => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DuplicativeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DuplicativeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DuplicativeIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DuplicativeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DuplicativeIndicator

/-- System Event Message: 11 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 64
  eventCode : EventCode
  sourceVenue : BitVec 16
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (EventCode.encode message.eventCode
    ++ (encodeUIntLE 2 message.sourceVenue))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  pure ({ timestamp, eventCode, sourceVenue }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SystemEventMessage

/-- Instrument Directory Message: 138 bytes -/
structure InstrumentDirectoryMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  isin : Alpha 12
  allowedBookTypes : BitVec 8
  sourceVenue : BitVec 16
  venueInstrumentId : Alpha 11
  tickId : Alpha 2
  priceBandTolerances : BitVec 64
  dynamicCircuitBreakerTolerances : BitVec 64
  staticCircuitBreakerTolerances : BitVec 64
  segment : Alpha 6
  reserved12 : Alpha 12
  securityExchange : Alpha 11
  currency : Alpha 3
  reserved1 : Alpha 1
  reserved4 : Alpha 4
  averageDailyTurnoverAdt : BitVec 64
  reserved8 : Alpha 8
  secondReserved1 : Alpha 1
  secondReserved8 : Alpha 8
  thirdReserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace InstrumentDirectoryMessage

def encode (message : InstrumentDirectoryMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (Alpha.encode message.isin
    ++ (encodeUIntLE 1 message.allowedBookTypes
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (Alpha.encode message.venueInstrumentId
    ++ (Alpha.encode message.tickId
    ++ (encodeUIntLE 8 message.priceBandTolerances
    ++ (encodeUIntLE 8 message.dynamicCircuitBreakerTolerances
    ++ (encodeUIntLE 8 message.staticCircuitBreakerTolerances
    ++ (Alpha.encode message.segment
    ++ (Alpha.encode message.reserved12
    ++ (Alpha.encode message.securityExchange
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 8 message.averageDailyTurnoverAdt
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.secondReserved1
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.thirdReserved8))))))))))))))))))))

def decode (bytes : List UInt8) : Option (InstrumentDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (allowedBookTypes, bytes) ← decodeUIntLE 1 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (venueInstrumentId, bytes) ← Alpha.decode 11 bytes
  let (tickId, bytes) ← Alpha.decode 2 bytes
  let (priceBandTolerances, bytes) ← decodeUIntLE 8 bytes
  let (dynamicCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (staticCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (segment, bytes) ← Alpha.decode 6 bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  let (securityExchange, bytes) ← Alpha.decode 11 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (averageDailyTurnoverAdt, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (thirdReserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ timestamp, instrument, isin, allowedBookTypes, sourceVenue, venueInstrumentId, tickId, priceBandTolerances, dynamicCircuitBreakerTolerances, staticCircuitBreakerTolerances, segment, reserved12, securityExchange, currency, reserved1, reserved4, averageDailyTurnoverAdt, reserved8, secondReserved1, secondReserved8, thirdReserved8 }, bytes)

@[simp] theorem encode_length (message : InstrumentDirectoryMessage) : (encode message).length = 138 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentDirectoryMessage

/-- Instrument Status Message: 27 bytes -/
structure InstrumentStatusMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  sourceVenue : BitVec 16
  tradingStatus : TradingStatus
  sessionChangeReason : BitVec 8
  newEndTime : Alpha 6
  orderBookType : BitVec 8
  deriving DecidableEq, Repr

namespace InstrumentStatusMessage

def encode (message : InstrumentStatusMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (TradingStatus.encode message.tradingStatus
    ++ (encodeUIntLE 1 message.sessionChangeReason
    ++ (Alpha.encode message.newEndTime
    ++ (encodeUIntLE 1 message.orderBookType))))))

def decode (bytes : List UInt8) : Option (InstrumentStatusMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (sessionChangeReason, bytes) ← decodeUIntLE 1 bytes
  let (newEndTime, bytes) ← Alpha.decode 6 bytes
  let (orderBookType, bytes) ← decodeUIntLE 1 bytes
  pure ({ timestamp, instrument, sourceVenue, tradingStatus, sessionChangeReason, newEndTime, orderBookType }, bytes)

@[simp] theorem encode_length (message : InstrumentStatusMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradingStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InstrumentStatusMessage

/-- Statistics Message: 74 bytes -/
structure StatisticsMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  sourceVenue : BitVec 16
  volume : BitVec 64
  volumeOnbookOnly : BitVec 64
  vwap : BitVec 64
  vwapOnbookOnly : BitVec 64
  numberOfTrades : BitVec 32
  numberOfTradesOnbookOnly : BitVec 32
  turnover : BitVec 64
  turnoverOnbookOnly : BitVec 64
  deriving DecidableEq, Repr

namespace StatisticsMessage

def encode (message : StatisticsMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.volume
    ++ (encodeUIntLE 8 message.volumeOnbookOnly
    ++ (encodeUIntLE 8 message.vwap
    ++ (encodeUIntLE 8 message.vwapOnbookOnly
    ++ (encodeUIntLE 4 message.numberOfTrades
    ++ (encodeUIntLE 4 message.numberOfTradesOnbookOnly
    ++ (encodeUIntLE 8 message.turnover
    ++ (encodeUIntLE 8 message.turnoverOnbookOnly))))))))))

def decode (bytes : List UInt8) : Option (StatisticsMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (volume, bytes) ← decodeUIntLE 8 bytes
  let (volumeOnbookOnly, bytes) ← decodeUIntLE 8 bytes
  let (vwap, bytes) ← decodeUIntLE 8 bytes
  let (vwapOnbookOnly, bytes) ← decodeUIntLE 8 bytes
  let (numberOfTrades, bytes) ← decodeUIntLE 4 bytes
  let (numberOfTradesOnbookOnly, bytes) ← decodeUIntLE 4 bytes
  let (turnover, bytes) ← decodeUIntLE 8 bytes
  let (turnoverOnbookOnly, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, instrument, sourceVenue, volume, volumeOnbookOnly, vwap, vwapOnbookOnly, numberOfTrades, numberOfTradesOnbookOnly, turnover, turnoverOnbookOnly }, bytes)

@[simp] theorem encode_length (message : StatisticsMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

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

end StatisticsMessage

/-- Mifid Ii Trade Report Message: 533 bytes -/
structure MifidIiTradeReportMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  transactionIdentificationCode : Alpha 52
  totalNumberOfTransactions : BitVec 32
  reserved8 : Alpha 8
  sourceVenue : BitVec 16
  price : Alpha 20
  quantity : Alpha 20
  tradingDateAndTime : Alpha 27
  instrumentIdentificationCodeType : Alpha 4
  instrumentIdentificationCode : Alpha 12
  priceNotation : Alpha 4
  priceMajorCurrencyPriceCurrency : Alpha 3
  notionalAmount : Alpha 20
  notionalCurrency : Alpha 3
  venueOfExecution : Alpha 4
  publicationDateAndTime : Alpha 27
  benchmarkTransactionFlag : Alpha 4
  agencyCrossTradeFlag : Alpha 4
  nonPriceFormingTransactionsFlag : Alpha 4
  nonPriceContributionToDiscovery : Alpha 4
  specialDividendFlag : Alpha 4
  ptDeferralReasonFlag : Alpha 4
  referencePriceTransactionFlag : Alpha 4
  ntLiquidityFlag : Alpha 4
  ntPriceConditionsFlag : Alpha 4
  algoTransactionFlag : Alpha 4
  ptIlliquidFlag : Alpha 4
  priceImprovementFlag : Alpha 4
  cancellationFlag : Alpha 4
  amendmentFlag : Alpha 4
  duplicateFlag : Alpha 4
  exchangeForPhysicalsFlag : Alpha 4
  limitedDetailsFlag : Alpha 4
  ldFullDetailsFlag : Alpha 4
  dailyAggregatedTransactionFlag : Alpha 4
  daFullDetailsFlag : Alpha 4
  volumeOmissionFlag : Alpha 4
  voFullDetailsFlag : Alpha 4
  fourWeeksAggregationFlag : Alpha 4
  faFullDetailsFlag : Alpha 4
  indefiniteAggregationFlag : Alpha 4
  volumeOmissionForSovereignDebtFlag : Alpha 4
  consecutiveAggregationFlag : Alpha 4
  reserved1 : Alpha 1
  venueType : BitVec 8
  venueBookDefinitionId : BitVec 8
  notationOfTheQuantityInMeasurementUnit : Alpha 25
  quantityInMeasurementUnit : Alpha 20
  transactionToBeCleared : TransactionToBeCleared
  emissionAllowanceType : Alpha 4
  venueOfPublication : Alpha 4
  marketMechanism : MarketMechanism
  tradingMode : TradingMode
  transactionCategory : TransactionCategory
  negotiationIndicator : NegotiationIndicator
  agencyCrossIndicator : AgencyCrossIndicator
  modificationIndicator : ModificationIndicator
  referencePriceIndicator : ReferencePriceIndicator
  specialDividendIndicator : SpecialDividendIndicator
  offBookAutomatedIndicator : OffBookAutomatedIndicator
  priceFormationIndicator : PriceFormationIndicator
  algorithmicIndicator : AlgorithmicIndicator
  postTradeDeferralReason : PostTradeDeferralReason
  deferralEnrichmentType : DeferralEnrichmentType
  duplicativeIndicator : DuplicativeIndicator
  thirdcountryTradingVenueOfExecution : Alpha 4
  portfolioTransactionFlag : Alpha 4
  contingentTransactionFlag : Alpha 4
  missingPricePriceConditions : Alpha 4
  marketClosingPriceFlag : Alpha 4
  ntLargeInScaleFlag : Alpha 4
  ntPreTradeTransparencyFlag : Alpha 4
  effectiveDateOfTheContract : Alpha 10
  maturityDateOfTheContract : Alpha 10
  spread : Alpha 20
  upfrontPayment : Alpha 20
  leiOfClearingHouse : Alpha 20
  matchedPrincipalTradeFlag : Alpha 4
  esmaStandardDeferralFlags : Alpha 4
  negotiationTradeFlag : Alpha 4
  esmaSupplementaryDeferralFlags : Alpha 4
  tradingSystem : Alpha 4
  deriving DecidableEq, Repr

namespace MifidIiTradeReportMessage

def encode (message : MifidIiTradeReportMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (Alpha.encode message.transactionIdentificationCode
    ++ (encodeUIntLE 4 message.totalNumberOfTransactions
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.tradingDateAndTime
    ++ (Alpha.encode message.instrumentIdentificationCodeType
    ++ (Alpha.encode message.instrumentIdentificationCode
    ++ (Alpha.encode message.priceNotation
    ++ (Alpha.encode message.priceMajorCurrencyPriceCurrency
    ++ (Alpha.encode message.notionalAmount
    ++ (Alpha.encode message.notionalCurrency
    ++ (Alpha.encode message.venueOfExecution
    ++ (Alpha.encode message.publicationDateAndTime
    ++ (Alpha.encode message.benchmarkTransactionFlag
    ++ (Alpha.encode message.agencyCrossTradeFlag
    ++ (Alpha.encode message.nonPriceFormingTransactionsFlag
    ++ (Alpha.encode message.nonPriceContributionToDiscovery
    ++ (Alpha.encode message.specialDividendFlag
    ++ (Alpha.encode message.ptDeferralReasonFlag
    ++ (Alpha.encode message.referencePriceTransactionFlag
    ++ (Alpha.encode message.ntLiquidityFlag
    ++ (Alpha.encode message.ntPriceConditionsFlag
    ++ (Alpha.encode message.algoTransactionFlag
    ++ (Alpha.encode message.ptIlliquidFlag
    ++ (Alpha.encode message.priceImprovementFlag
    ++ (Alpha.encode message.cancellationFlag
    ++ (Alpha.encode message.amendmentFlag
    ++ (Alpha.encode message.duplicateFlag
    ++ (Alpha.encode message.exchangeForPhysicalsFlag
    ++ (Alpha.encode message.limitedDetailsFlag
    ++ (Alpha.encode message.ldFullDetailsFlag
    ++ (Alpha.encode message.dailyAggregatedTransactionFlag
    ++ (Alpha.encode message.daFullDetailsFlag
    ++ (Alpha.encode message.volumeOmissionFlag
    ++ (Alpha.encode message.voFullDetailsFlag
    ++ (Alpha.encode message.fourWeeksAggregationFlag
    ++ (Alpha.encode message.faFullDetailsFlag
    ++ (Alpha.encode message.indefiniteAggregationFlag
    ++ (Alpha.encode message.volumeOmissionForSovereignDebtFlag
    ++ (Alpha.encode message.consecutiveAggregationFlag
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 1 message.venueType
    ++ (encodeUIntLE 1 message.venueBookDefinitionId
    ++ (Alpha.encode message.notationOfTheQuantityInMeasurementUnit
    ++ (Alpha.encode message.quantityInMeasurementUnit
    ++ (TransactionToBeCleared.encode message.transactionToBeCleared
    ++ (Alpha.encode message.emissionAllowanceType
    ++ (Alpha.encode message.venueOfPublication
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (TradingMode.encode message.tradingMode
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (NegotiationIndicator.encode message.negotiationIndicator
    ++ (AgencyCrossIndicator.encode message.agencyCrossIndicator
    ++ (ModificationIndicator.encode message.modificationIndicator
    ++ (ReferencePriceIndicator.encode message.referencePriceIndicator
    ++ (SpecialDividendIndicator.encode message.specialDividendIndicator
    ++ (OffBookAutomatedIndicator.encode message.offBookAutomatedIndicator
    ++ (PriceFormationIndicator.encode message.priceFormationIndicator
    ++ (AlgorithmicIndicator.encode message.algorithmicIndicator
    ++ (PostTradeDeferralReason.encode message.postTradeDeferralReason
    ++ (DeferralEnrichmentType.encode message.deferralEnrichmentType
    ++ (DuplicativeIndicator.encode message.duplicativeIndicator
    ++ (Alpha.encode message.thirdcountryTradingVenueOfExecution
    ++ (Alpha.encode message.portfolioTransactionFlag
    ++ (Alpha.encode message.contingentTransactionFlag
    ++ (Alpha.encode message.missingPricePriceConditions
    ++ (Alpha.encode message.marketClosingPriceFlag
    ++ (Alpha.encode message.ntLargeInScaleFlag
    ++ (Alpha.encode message.ntPreTradeTransparencyFlag
    ++ (Alpha.encode message.effectiveDateOfTheContract
    ++ (Alpha.encode message.maturityDateOfTheContract
    ++ (Alpha.encode message.spread
    ++ (Alpha.encode message.upfrontPayment
    ++ (Alpha.encode message.leiOfClearingHouse
    ++ (Alpha.encode message.matchedPrincipalTradeFlag
    ++ (Alpha.encode message.esmaStandardDeferralFlags
    ++ (Alpha.encode message.negotiationTradeFlag
    ++ (Alpha.encode message.esmaSupplementaryDeferralFlags
    ++ (Alpha.encode message.tradingSystem))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MifidIiTradeReportMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (transactionIdentificationCode, bytes) ← Alpha.decode 52 bytes
  let (totalNumberOfTransactions, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (price, bytes) ← Alpha.decode 20 bytes
  let (quantity, bytes) ← Alpha.decode 20 bytes
  let (tradingDateAndTime, bytes) ← Alpha.decode 27 bytes
  let (instrumentIdentificationCodeType, bytes) ← Alpha.decode 4 bytes
  let (instrumentIdentificationCode, bytes) ← Alpha.decode 12 bytes
  let (priceNotation, bytes) ← Alpha.decode 4 bytes
  let (priceMajorCurrencyPriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (notionalAmount, bytes) ← Alpha.decode 20 bytes
  let (notionalCurrency, bytes) ← Alpha.decode 3 bytes
  let (venueOfExecution, bytes) ← Alpha.decode 4 bytes
  let (publicationDateAndTime, bytes) ← Alpha.decode 27 bytes
  let (benchmarkTransactionFlag, bytes) ← Alpha.decode 4 bytes
  let (agencyCrossTradeFlag, bytes) ← Alpha.decode 4 bytes
  let (nonPriceFormingTransactionsFlag, bytes) ← Alpha.decode 4 bytes
  let (nonPriceContributionToDiscovery, bytes) ← Alpha.decode 4 bytes
  let (specialDividendFlag, bytes) ← Alpha.decode 4 bytes
  let (ptDeferralReasonFlag, bytes) ← Alpha.decode 4 bytes
  let (referencePriceTransactionFlag, bytes) ← Alpha.decode 4 bytes
  let (ntLiquidityFlag, bytes) ← Alpha.decode 4 bytes
  let (ntPriceConditionsFlag, bytes) ← Alpha.decode 4 bytes
  let (algoTransactionFlag, bytes) ← Alpha.decode 4 bytes
  let (ptIlliquidFlag, bytes) ← Alpha.decode 4 bytes
  let (priceImprovementFlag, bytes) ← Alpha.decode 4 bytes
  let (cancellationFlag, bytes) ← Alpha.decode 4 bytes
  let (amendmentFlag, bytes) ← Alpha.decode 4 bytes
  let (duplicateFlag, bytes) ← Alpha.decode 4 bytes
  let (exchangeForPhysicalsFlag, bytes) ← Alpha.decode 4 bytes
  let (limitedDetailsFlag, bytes) ← Alpha.decode 4 bytes
  let (ldFullDetailsFlag, bytes) ← Alpha.decode 4 bytes
  let (dailyAggregatedTransactionFlag, bytes) ← Alpha.decode 4 bytes
  let (daFullDetailsFlag, bytes) ← Alpha.decode 4 bytes
  let (volumeOmissionFlag, bytes) ← Alpha.decode 4 bytes
  let (voFullDetailsFlag, bytes) ← Alpha.decode 4 bytes
  let (fourWeeksAggregationFlag, bytes) ← Alpha.decode 4 bytes
  let (faFullDetailsFlag, bytes) ← Alpha.decode 4 bytes
  let (indefiniteAggregationFlag, bytes) ← Alpha.decode 4 bytes
  let (volumeOmissionForSovereignDebtFlag, bytes) ← Alpha.decode 4 bytes
  let (consecutiveAggregationFlag, bytes) ← Alpha.decode 4 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (venueType, bytes) ← decodeUIntLE 1 bytes
  let (venueBookDefinitionId, bytes) ← decodeUIntLE 1 bytes
  let (notationOfTheQuantityInMeasurementUnit, bytes) ← Alpha.decode 25 bytes
  let (quantityInMeasurementUnit, bytes) ← Alpha.decode 20 bytes
  let (transactionToBeCleared, bytes) ← TransactionToBeCleared.decode bytes
  let (emissionAllowanceType, bytes) ← Alpha.decode 4 bytes
  let (venueOfPublication, bytes) ← Alpha.decode 4 bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (tradingMode, bytes) ← TradingMode.decode bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (negotiationIndicator, bytes) ← NegotiationIndicator.decode bytes
  let (agencyCrossIndicator, bytes) ← AgencyCrossIndicator.decode bytes
  let (modificationIndicator, bytes) ← ModificationIndicator.decode bytes
  let (referencePriceIndicator, bytes) ← ReferencePriceIndicator.decode bytes
  let (specialDividendIndicator, bytes) ← SpecialDividendIndicator.decode bytes
  let (offBookAutomatedIndicator, bytes) ← OffBookAutomatedIndicator.decode bytes
  let (priceFormationIndicator, bytes) ← PriceFormationIndicator.decode bytes
  let (algorithmicIndicator, bytes) ← AlgorithmicIndicator.decode bytes
  let (postTradeDeferralReason, bytes) ← PostTradeDeferralReason.decode bytes
  let (deferralEnrichmentType, bytes) ← DeferralEnrichmentType.decode bytes
  let (duplicativeIndicator, bytes) ← DuplicativeIndicator.decode bytes
  let (thirdcountryTradingVenueOfExecution, bytes) ← Alpha.decode 4 bytes
  let (portfolioTransactionFlag, bytes) ← Alpha.decode 4 bytes
  let (contingentTransactionFlag, bytes) ← Alpha.decode 4 bytes
  let (missingPricePriceConditions, bytes) ← Alpha.decode 4 bytes
  let (marketClosingPriceFlag, bytes) ← Alpha.decode 4 bytes
  let (ntLargeInScaleFlag, bytes) ← Alpha.decode 4 bytes
  let (ntPreTradeTransparencyFlag, bytes) ← Alpha.decode 4 bytes
  let (effectiveDateOfTheContract, bytes) ← Alpha.decode 10 bytes
  let (maturityDateOfTheContract, bytes) ← Alpha.decode 10 bytes
  let (spread, bytes) ← Alpha.decode 20 bytes
  let (upfrontPayment, bytes) ← Alpha.decode 20 bytes
  let (leiOfClearingHouse, bytes) ← Alpha.decode 20 bytes
  let (matchedPrincipalTradeFlag, bytes) ← Alpha.decode 4 bytes
  let (esmaStandardDeferralFlags, bytes) ← Alpha.decode 4 bytes
  let (negotiationTradeFlag, bytes) ← Alpha.decode 4 bytes
  let (esmaSupplementaryDeferralFlags, bytes) ← Alpha.decode 4 bytes
  let (tradingSystem, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, instrument, transactionIdentificationCode, totalNumberOfTransactions, reserved8, sourceVenue, price, quantity, tradingDateAndTime, instrumentIdentificationCodeType, instrumentIdentificationCode, priceNotation, priceMajorCurrencyPriceCurrency, notionalAmount, notionalCurrency, venueOfExecution, publicationDateAndTime, benchmarkTransactionFlag, agencyCrossTradeFlag, nonPriceFormingTransactionsFlag, nonPriceContributionToDiscovery, specialDividendFlag, ptDeferralReasonFlag, referencePriceTransactionFlag, ntLiquidityFlag, ntPriceConditionsFlag, algoTransactionFlag, ptIlliquidFlag, priceImprovementFlag, cancellationFlag, amendmentFlag, duplicateFlag, exchangeForPhysicalsFlag, limitedDetailsFlag, ldFullDetailsFlag, dailyAggregatedTransactionFlag, daFullDetailsFlag, volumeOmissionFlag, voFullDetailsFlag, fourWeeksAggregationFlag, faFullDetailsFlag, indefiniteAggregationFlag, volumeOmissionForSovereignDebtFlag, consecutiveAggregationFlag, reserved1, venueType, venueBookDefinitionId, notationOfTheQuantityInMeasurementUnit, quantityInMeasurementUnit, transactionToBeCleared, emissionAllowanceType, venueOfPublication, marketMechanism, tradingMode, transactionCategory, negotiationIndicator, agencyCrossIndicator, modificationIndicator, referencePriceIndicator, specialDividendIndicator, offBookAutomatedIndicator, priceFormationIndicator, algorithmicIndicator, postTradeDeferralReason, deferralEnrichmentType, duplicativeIndicator, thirdcountryTradingVenueOfExecution, portfolioTransactionFlag, contingentTransactionFlag, missingPricePriceConditions, marketClosingPriceFlag, ntLargeInScaleFlag, ntPreTradeTransparencyFlag, effectiveDateOfTheContract, maturityDateOfTheContract, spread, upfrontPayment, leiOfClearingHouse, matchedPrincipalTradeFlag, esmaStandardDeferralFlags, negotiationTradeFlag, esmaSupplementaryDeferralFlags, tradingSystem }, bytes)

@[simp] theorem encode_length (message : MifidIiTradeReportMessage) : (encode message).length = 533 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TransactionToBeCleared.encode_length, MarketMechanism.encode_length, TradingMode.encode_length, TransactionCategory.encode_length, NegotiationIndicator.encode_length, AgencyCrossIndicator.encode_length, ModificationIndicator.encode_length, ReferencePriceIndicator.encode_length, SpecialDividendIndicator.encode_length, OffBookAutomatedIndicator.encode_length, PriceFormationIndicator.encode_length, AlgorithmicIndicator.encode_length, PostTradeDeferralReason.encode_length, DeferralEnrichmentType.encode_length, DuplicativeIndicator.encode_length]

theorem encode_length_pos (message : MifidIiTradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MifidIiTradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionToBeCleared.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingMode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NegotiationIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AgencyCrossIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ModificationIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReferencePriceIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialDividendIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OffBookAutomatedIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceFormationIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AlgorithmicIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PostTradeDeferralReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeferralEnrichmentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DuplicativeIndicator.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end MifidIiTradeReportMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- 83
  | instrumentDirectoryMessage (message : InstrumentDirectoryMessage) -- 112
  | instrumentStatusMessage (message : InstrumentStatusMessage) -- 72
  | statisticsMessage (message : StatisticsMessage) -- 119
  | mifidIiTradeReportMessage (message : MifidIiTradeReportMessage) -- 84
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .instrumentDirectoryMessage _ => 112
  | .instrumentStatusMessage _ => 72
  | .statisticsMessage _ => 119
  | .mifidIiTradeReportMessage _ => 84

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .instrumentDirectoryMessage message => InstrumentDirectoryMessage.encode message
  | .instrumentStatusMessage message => InstrumentStatusMessage.encode message
  | .statisticsMessage message => StatisticsMessage.encode message
  | .mifidIiTradeReportMessage message => MifidIiTradeReportMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 533 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | instrumentDirectoryMessage inner =>
    simp only [encode, InstrumentDirectoryMessage.encode_length]
    omega
  | instrumentStatusMessage inner =>
    simp only [encode, InstrumentStatusMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [encode, StatisticsMessage.encode_length]
    omega
  | mifidIiTradeReportMessage inner =>
    simp only [encode, MifidIiTradeReportMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 112 then (InstrumentDirectoryMessage.decode bytes).map fun (message, rest) => (.instrumentDirectoryMessage message, rest)
  else if tag = 72 then (InstrumentStatusMessage.decode bytes).map fun (message, rest) => (.instrumentStatusMessage message, rest)
  else if tag = 119 then (StatisticsMessage.decode bytes).map fun (message, rest) => (.statisticsMessage message, rest)
  else if tag = 84 then (MifidIiTradeReportMessage.decode bytes).map fun (message, rest) => (.mifidIiTradeReportMessage message, rest)
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
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | instrumentDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InstrumentDirectoryMessage.encode_length]
    omega
  | instrumentStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InstrumentStatusMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsMessage.encode_length]
    omega
  | mifidIiTradeReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MifidIiTradeReportMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
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
  length : BitVec 16
  marketDataGroup : Alpha 1
  sequenceNumber : BitVec 32
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.length
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (Alpha.encode message.marketDataGroup
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeMany Message.encode message.message.val))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (length, bytes) ← decodeUIntLE 2 bytes
  let (messageCount, bytes) ← decodeUIntLE 1 bytes
  let (marketDataGroup, bytes) ← Alpha.decode 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ length, marketDataGroup, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.LsegTradeechoMifid2posttradeGtpV2722
