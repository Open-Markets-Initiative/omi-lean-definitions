import Omi.Wire

/-!
# Investors Exchange Top Of Book v1.66

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: Security Directory Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Quote Update Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Sale Condition Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.IexIexequitiesTopsIextpV166

/-- Message Type: one byte code -/
inductive MessageType where
  | systemEventMessage -- System Event Message
  | securityDirectoryMessage -- Security Directory Message
  | tradingStatusMessage -- Trading Status Message
  | retailLiquidityIndicatorMessage -- Retail Liquidity Indicator Message
  | operationalHaltStatusMessage -- Operational Halt Status Message
  | shortSalePriceTestStatusMessage -- Short Sale Price Test Status Message
  | quoteUpdateMessage -- Quote Update Message
  | tradeReportMessage -- Trade Report Message
  | officialPriceMessage -- Official Price Message
  | tradeBreakMessage -- Trade Break Message
  | auctionInformationMessage -- Auction Information Message
  deriving DecidableEq, Repr

namespace MessageType

def toByte : MessageType → UInt8
  | .systemEventMessage => 0x53
  | .securityDirectoryMessage => 0x44
  | .tradingStatusMessage => 0x48
  | .retailLiquidityIndicatorMessage => 0x49
  | .operationalHaltStatusMessage => 0x4F
  | .shortSalePriceTestStatusMessage => 0x50
  | .quoteUpdateMessage => 0x51
  | .tradeReportMessage => 0x54
  | .officialPriceMessage => 0x58
  | .tradeBreakMessage => 0x42
  | .auctionInformationMessage => 0x41

def ofByte? (byte : UInt8) : Option MessageType :=
  if byte = 0x53 then some .systemEventMessage
  else if byte = 0x44 then some .securityDirectoryMessage
  else if byte = 0x48 then some .tradingStatusMessage
  else if byte = 0x49 then some .retailLiquidityIndicatorMessage
  else if byte = 0x4F then some .operationalHaltStatusMessage
  else if byte = 0x50 then some .shortSalePriceTestStatusMessage
  else if byte = 0x51 then some .quoteUpdateMessage
  else if byte = 0x54 then some .tradeReportMessage
  else if byte = 0x58 then some .officialPriceMessage
  else if byte = 0x42 then some .tradeBreakMessage
  else if byte = 0x41 then some .auctionInformationMessage
  else none

theorem ofByte?_toByte (value : MessageType) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : MessageType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MessageType × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : MessageType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MessageType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end MessageType

/-- System Event: one byte code -/
inductive SystemEvent where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfRegularMarketHours -- Start Of Regular Market Hours
  | endOfRegularMarketHours -- End Of Regular Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  deriving DecidableEq, Repr

namespace SystemEvent

def toByte : SystemEvent → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfRegularMarketHours => 0x52
  | .endOfRegularMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43

def ofByte? (byte : UInt8) : Option SystemEvent :=
  if byte = 0x4F then some .startOfMessages
  else if byte = 0x53 then some .startOfSystemHours
  else if byte = 0x52 then some .startOfRegularMarketHours
  else if byte = 0x4D then some .endOfRegularMarketHours
  else if byte = 0x45 then some .endOfSystemHours
  else if byte = 0x43 then some .endOfMessages
  else none

theorem ofByte?_toByte (value : SystemEvent) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : SystemEvent) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SystemEvent × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : SystemEvent) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SystemEvent) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end SystemEvent

/-- Trading Status: one byte code -/
inductive TradingStatus where
  | tradingHaltedAcrossAllUsEquityMarkets -- Trading Halted Across All Us Equity Markets
  | tradingHaltReleasedIntoAnOrderAcceptancePeriodOnIex -- Trading Halt Released Into An Order Acceptance Period On Iex
  | tradingPausedAndOrderAcceptancePeriodOnIex -- Trading Paused And Order Acceptance Period On Iex
  | tradingOnIex -- Trading On Iex
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .tradingHaltedAcrossAllUsEquityMarkets => 0x48
  | .tradingHaltReleasedIntoAnOrderAcceptancePeriodOnIex => 0x4F
  | .tradingPausedAndOrderAcceptancePeriodOnIex => 0x50
  | .tradingOnIex => 0x54

def ofByte? (byte : UInt8) : Option TradingStatus :=
  if byte = 0x48 then some .tradingHaltedAcrossAllUsEquityMarkets
  else if byte = 0x4F then some .tradingHaltReleasedIntoAnOrderAcceptancePeriodOnIex
  else if byte = 0x50 then some .tradingPausedAndOrderAcceptancePeriodOnIex
  else if byte = 0x54 then some .tradingOnIex
  else none

theorem ofByte?_toByte (value : TradingStatus) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : TradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingStatus × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end TradingStatus

/-- Retail Liquidity Indicator: one byte code -/
inductive RetailLiquidityIndicator where
  | notApplicable -- Not Applicable
  | buyInterest -- Buy Interest
  | sellInterest -- Sell Interest
  | buyAndSellInterest -- Buy And Sell Interest
  deriving DecidableEq, Repr

namespace RetailLiquidityIndicator

def toByte : RetailLiquidityIndicator → UInt8
  | .notApplicable => 0x20
  | .buyInterest => 0x41
  | .sellInterest => 0x42
  | .buyAndSellInterest => 0x43

def ofByte? (byte : UInt8) : Option RetailLiquidityIndicator :=
  if byte = 0x20 then some .notApplicable
  else if byte = 0x41 then some .buyInterest
  else if byte = 0x42 then some .sellInterest
  else if byte = 0x43 then some .buyAndSellInterest
  else none

theorem ofByte?_toByte (value : RetailLiquidityIndicator) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : RetailLiquidityIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetailLiquidityIndicator × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : RetailLiquidityIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RetailLiquidityIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end RetailLiquidityIndicator

/-- Operational Halt Status: one byte code -/
inductive OperationalHaltStatus where
  | iexSpecificOperationalTradingHalt -- Iex Specific Operational Trading Halt
  | notOperationallyHaltedOnIex -- Not Operationally Halted On Iex
  deriving DecidableEq, Repr

namespace OperationalHaltStatus

def toByte : OperationalHaltStatus → UInt8
  | .iexSpecificOperationalTradingHalt => 0x4F
  | .notOperationallyHaltedOnIex => 0x4E

def ofByte? (byte : UInt8) : Option OperationalHaltStatus :=
  if byte = 0x4F then some .iexSpecificOperationalTradingHalt
  else if byte = 0x4E then some .notOperationallyHaltedOnIex
  else none

theorem ofByte?_toByte (value : OperationalHaltStatus) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : OperationalHaltStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OperationalHaltStatus × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : OperationalHaltStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OperationalHaltStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end OperationalHaltStatus

/-- Detail: one byte code -/
inductive Detail where
  | noPriceTestInPlace -- No Price Test In Place
  | activated -- Activated
  | continued -- Continued
  | deactivated -- Deactivated
  | notAvailable -- Not Available
  deriving DecidableEq, Repr

namespace Detail

def toByte : Detail → UInt8
  | .noPriceTestInPlace => 0x20
  | .activated => 0x41
  | .continued => 0x43
  | .deactivated => 0x44
  | .notAvailable => 0x4E

def ofByte? (byte : UInt8) : Option Detail :=
  if byte = 0x20 then some .noPriceTestInPlace
  else if byte = 0x41 then some .activated
  else if byte = 0x43 then some .continued
  else if byte = 0x44 then some .deactivated
  else if byte = 0x4E then some .notAvailable
  else none

theorem ofByte?_toByte (value : Detail) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : Detail) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Detail × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : Detail) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Detail) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end Detail

/-- Price Type: one byte code -/
inductive PriceType where
  | iexOfficialOpeningPrice -- Iex Official Opening Price
  | iexOfficialClosingPrice -- Iex Official Closing Price
  deriving DecidableEq, Repr

namespace PriceType

def toByte : PriceType → UInt8
  | .iexOfficialOpeningPrice => 0x51
  | .iexOfficialClosingPrice => 0x4D

def ofByte? (byte : UInt8) : Option PriceType :=
  if byte = 0x51 then some .iexOfficialOpeningPrice
  else if byte = 0x4D then some .iexOfficialClosingPrice
  else none

theorem ofByte?_toByte (value : PriceType) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : PriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceType × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end PriceType

/-- Auction Type: one byte code -/
inductive AuctionType where
  | openingAuction -- Opening Auction
  | closingAuction -- Closing Auction
  | ipoAuction -- Ipo Auction
  | haltAuction -- Halt Auction
  | volatilityAuction -- Volatility Auction
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .openingAuction => 0x4F
  | .closingAuction => 0x43
  | .ipoAuction => 0x49
  | .haltAuction => 0x48
  | .volatilityAuction => 0x56

def ofByte? (byte : UInt8) : Option AuctionType :=
  if byte = 0x4F then some .openingAuction
  else if byte = 0x43 then some .closingAuction
  else if byte = 0x49 then some .ipoAuction
  else if byte = 0x48 then some .haltAuction
  else if byte = 0x56 then some .volatilityAuction
  else none

theorem ofByte?_toByte (value : AuctionType) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : AuctionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionType × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AuctionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end AuctionType

/-- Imbalance Side: one byte code -/
inductive ImbalanceSide where
  | buy -- Buy
  | sell -- Sell
  | none_ -- None
  deriving DecidableEq, Repr

namespace ImbalanceSide

def toByte : ImbalanceSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .none_ => 0x4E

def ofByte? (byte : UInt8) : Option ImbalanceSide :=
  if byte = 0x42 then some .buy
  else if byte = 0x53 then some .sell
  else if byte = 0x4E then some .none_
  else none

theorem ofByte?_toByte (value : ImbalanceSide) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : ImbalanceSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceSide × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ImbalanceSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end ImbalanceSide

/-- System Event Message: 9 bytes -/
structure SystemEventMessage where
  systemEvent : SystemEvent
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  SystemEvent.encode message.systemEvent
    ++ encodeUIntLE 8 message.timestamp

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (systemEvent, bytes) ← SystemEvent.decode bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ systemEvent, timestamp }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 9 := by
  simp [encode]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end SystemEventMessage

/-- Security Directory Message: 30 bytes -/
structure SecurityDirectoryMessage where
  securityDirectoryFlags : BitVec 8
  timestamp : BitVec 64
  symbol : Alpha 8
  roundLotSize : BitVec 32
  adjustedPocPrice : BitVec 64
  luldTier : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityDirectoryMessage

def encode (message : SecurityDirectoryMessage) : List UInt8 :=
  encodeUIntLE 1 message.securityDirectoryFlags
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 4 message.roundLotSize
    ++ encodeUIntLE 8 message.adjustedPocPrice
    ++ encodeUInt 1 message.luldTier

def decode (bytes : List UInt8) : Option (SecurityDirectoryMessage × List UInt8) := do
  let (securityDirectoryFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (roundLotSize, bytes) ← decodeUIntLE 4 bytes
  let (adjustedPocPrice, bytes) ← decodeUIntLE 8 bytes
  let (luldTier, bytes) ← decodeUInt 1 bytes
  pure ({ securityDirectoryFlags, timestamp, symbol, roundLotSize, adjustedPocPrice, luldTier }, bytes)

@[simp] theorem encode_length (message : SecurityDirectoryMessage) : (encode message).length = 30 := by
  simp [encode]

theorem encode_length_pos (message : SecurityDirectoryMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SecurityDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end SecurityDirectoryMessage

/-- Trading Status Message: 21 bytes -/
structure TradingStatusMessage where
  tradingStatus : TradingStatus
  timestamp : BitVec 64
  symbol : Alpha 8
  reason : Alpha 4
  deriving DecidableEq, Repr

namespace TradingStatusMessage

def encode (message : TradingStatusMessage) : List UInt8 :=
  TradingStatus.encode message.tradingStatus
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol
    ++ Alpha.encode message.reason

def decode (bytes : List UInt8) : Option (TradingStatusMessage × List UInt8) := do
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (reason, bytes) ← Alpha.decode 4 bytes
  pure ({ tradingStatus, timestamp, symbol, reason }, bytes)

@[simp] theorem encode_length (message : TradingStatusMessage) : (encode message).length = 21 := by
  simp [encode]

theorem encode_length_pos (message : TradingStatusMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TradingStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end TradingStatusMessage

/-- Retail Liquidity Indicator Message: 17 bytes -/
structure RetailLiquidityIndicatorMessage where
  retailLiquidityIndicator : RetailLiquidityIndicator
  timestamp : BitVec 64
  symbol : Alpha 8
  deriving DecidableEq, Repr

namespace RetailLiquidityIndicatorMessage

def encode (message : RetailLiquidityIndicatorMessage) : List UInt8 :=
  RetailLiquidityIndicator.encode message.retailLiquidityIndicator
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol

def decode (bytes : List UInt8) : Option (RetailLiquidityIndicatorMessage × List UInt8) := do
  let (retailLiquidityIndicator, bytes) ← RetailLiquidityIndicator.decode bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  pure ({ retailLiquidityIndicator, timestamp, symbol }, bytes)

@[simp] theorem encode_length (message : RetailLiquidityIndicatorMessage) : (encode message).length = 17 := by
  simp [encode]

theorem encode_length_pos (message : RetailLiquidityIndicatorMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : RetailLiquidityIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end RetailLiquidityIndicatorMessage

/-- Operational Halt Status Message: 17 bytes -/
structure OperationalHaltStatusMessage where
  operationalHaltStatus : OperationalHaltStatus
  timestamp : BitVec 64
  symbol : Alpha 8
  deriving DecidableEq, Repr

namespace OperationalHaltStatusMessage

def encode (message : OperationalHaltStatusMessage) : List UInt8 :=
  OperationalHaltStatus.encode message.operationalHaltStatus
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol

def decode (bytes : List UInt8) : Option (OperationalHaltStatusMessage × List UInt8) := do
  let (operationalHaltStatus, bytes) ← OperationalHaltStatus.decode bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  pure ({ operationalHaltStatus, timestamp, symbol }, bytes)

@[simp] theorem encode_length (message : OperationalHaltStatusMessage) : (encode message).length = 17 := by
  simp [encode]

theorem encode_length_pos (message : OperationalHaltStatusMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : OperationalHaltStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end OperationalHaltStatusMessage

/-- Short Sale Price Test Status Message: 18 bytes -/
structure ShortSalePriceTestStatusMessage where
  shortSalePriceTestStatus : BitVec 8
  timestamp : BitVec 64
  symbol : Alpha 8
  detail : Detail
  deriving DecidableEq, Repr

namespace ShortSalePriceTestStatusMessage

def encode (message : ShortSalePriceTestStatusMessage) : List UInt8 :=
  encodeUInt 1 message.shortSalePriceTestStatus
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol
    ++ Detail.encode message.detail

def decode (bytes : List UInt8) : Option (ShortSalePriceTestStatusMessage × List UInt8) := do
  let (shortSalePriceTestStatus, bytes) ← decodeUInt 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (detail, bytes) ← Detail.decode bytes
  pure ({ shortSalePriceTestStatus, timestamp, symbol, detail }, bytes)

@[simp] theorem encode_length (message : ShortSalePriceTestStatusMessage) : (encode message).length = 18 := by
  simp [encode]

theorem encode_length_pos (message : ShortSalePriceTestStatusMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ShortSalePriceTestStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end ShortSalePriceTestStatusMessage

/-- Quote Update Message: 41 bytes -/
structure QuoteUpdateMessage where
  quoteUpdateFlags : BitVec 8
  timestamp : BitVec 64
  symbol : Alpha 8
  bidSize : BitVec 32
  bidPrice : BitVec 64
  askPrice : BitVec 64
  askSize : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteUpdateMessage

def encode (message : QuoteUpdateMessage) : List UInt8 :=
  encodeUIntLE 1 message.quoteUpdateFlags
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 4 message.bidSize
    ++ encodeUIntLE 8 message.bidPrice
    ++ encodeUIntLE 8 message.askPrice
    ++ encodeUIntLE 4 message.askSize

def decode (bytes : List UInt8) : Option (QuoteUpdateMessage × List UInt8) := do
  let (quoteUpdateFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 8 bytes
  let (askPrice, bytes) ← decodeUIntLE 8 bytes
  let (askSize, bytes) ← decodeUIntLE 4 bytes
  pure ({ quoteUpdateFlags, timestamp, symbol, bidSize, bidPrice, askPrice, askSize }, bytes)

@[simp] theorem encode_length (message : QuoteUpdateMessage) : (encode message).length = 41 := by
  simp [encode]

theorem encode_length_pos (message : QuoteUpdateMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : QuoteUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end QuoteUpdateMessage

/-- Trade Report Message: 37 bytes -/
structure TradeReportMessage where
  saleConditionFlags : BitVec 8
  timestamp : BitVec 64
  symbol : Alpha 8
  size : BitVec 32
  price : BitVec 64
  tradeId : BitVec 64
  deriving DecidableEq, Repr

namespace TradeReportMessage

def encode (message : TradeReportMessage) : List UInt8 :=
  encodeUIntLE 1 message.saleConditionFlags
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 4 message.size
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.tradeId

def decode (bytes : List UInt8) : Option (TradeReportMessage × List UInt8) := do
  let (saleConditionFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  pure ({ saleConditionFlags, timestamp, symbol, size, price, tradeId }, bytes)

@[simp] theorem encode_length (message : TradeReportMessage) : (encode message).length = 37 := by
  simp [encode]

theorem encode_length_pos (message : TradeReportMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end TradeReportMessage

/-- Official Price Message: 25 bytes -/
structure OfficialPriceMessage where
  priceType : PriceType
  timestamp : BitVec 64
  symbol : Alpha 8
  officialPrice : BitVec 64
  deriving DecidableEq, Repr

namespace OfficialPriceMessage

def encode (message : OfficialPriceMessage) : List UInt8 :=
  PriceType.encode message.priceType
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.officialPrice

def decode (bytes : List UInt8) : Option (OfficialPriceMessage × List UInt8) := do
  let (priceType, bytes) ← PriceType.decode bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (officialPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ priceType, timestamp, symbol, officialPrice }, bytes)

@[simp] theorem encode_length (message : OfficialPriceMessage) : (encode message).length = 25 := by
  simp [encode]

theorem encode_length_pos (message : OfficialPriceMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : OfficialPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end OfficialPriceMessage

/-- Trade Break Message: 37 bytes -/
structure TradeBreakMessage where
  saleConditionFlags : BitVec 8
  timestamp : BitVec 64
  symbol : Alpha 8
  size : BitVec 32
  price : BitVec 64
  tradeId : BitVec 64
  deriving DecidableEq, Repr

namespace TradeBreakMessage

def encode (message : TradeBreakMessage) : List UInt8 :=
  encodeUIntLE 1 message.saleConditionFlags
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 4 message.size
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.tradeId

def decode (bytes : List UInt8) : Option (TradeBreakMessage × List UInt8) := do
  let (saleConditionFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  pure ({ saleConditionFlags, timestamp, symbol, size, price, tradeId }, bytes)

@[simp] theorem encode_length (message : TradeBreakMessage) : (encode message).length = 37 := by
  simp [encode]

theorem encode_length_pos (message : TradeBreakMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TradeBreakMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end TradeBreakMessage

/-- Auction Information Message: 79 bytes -/
structure AuctionInformationMessage where
  auctionType : AuctionType
  timestamp : BitVec 64
  symbol : Alpha 8
  pairedShares : BitVec 32
  referencePrice : BitVec 64
  indicativeClearingPrice : BitVec 64
  imbalanceShares : BitVec 32
  imbalanceSide : ImbalanceSide
  extensionNumber : Alpha 1
  scheduledAuctionTime : BitVec 32
  auctionBookClearingPrice : BitVec 64
  collarReferencePrice : BitVec 64
  lowerAuctionCollar : BitVec 64
  upperAuctionCollar : BitVec 64
  deriving DecidableEq, Repr

namespace AuctionInformationMessage

def encode (message : AuctionInformationMessage) : List UInt8 :=
  AuctionType.encode message.auctionType
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 4 message.pairedShares
    ++ encodeUIntLE 8 message.referencePrice
    ++ encodeUIntLE 8 message.indicativeClearingPrice
    ++ encodeUIntLE 4 message.imbalanceShares
    ++ ImbalanceSide.encode message.imbalanceSide
    ++ Alpha.encode message.extensionNumber
    ++ encodeUIntLE 4 message.scheduledAuctionTime
    ++ encodeUIntLE 8 message.auctionBookClearingPrice
    ++ encodeUIntLE 8 message.collarReferencePrice
    ++ encodeUIntLE 8 message.lowerAuctionCollar
    ++ encodeUIntLE 8 message.upperAuctionCollar

def decode (bytes : List UInt8) : Option (AuctionInformationMessage × List UInt8) := do
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (pairedShares, bytes) ← decodeUIntLE 4 bytes
  let (referencePrice, bytes) ← decodeUIntLE 8 bytes
  let (indicativeClearingPrice, bytes) ← decodeUIntLE 8 bytes
  let (imbalanceShares, bytes) ← decodeUIntLE 4 bytes
  let (imbalanceSide, bytes) ← ImbalanceSide.decode bytes
  let (extensionNumber, bytes) ← Alpha.decode 1 bytes
  let (scheduledAuctionTime, bytes) ← decodeUIntLE 4 bytes
  let (auctionBookClearingPrice, bytes) ← decodeUIntLE 8 bytes
  let (collarReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (lowerAuctionCollar, bytes) ← decodeUIntLE 8 bytes
  let (upperAuctionCollar, bytes) ← decodeUIntLE 8 bytes
  pure ({ auctionType, timestamp, symbol, pairedShares, referencePrice, indicativeClearingPrice, imbalanceShares, imbalanceSide, extensionNumber, scheduledAuctionTime, auctionBookClearingPrice, collarReferencePrice, lowerAuctionCollar, upperAuctionCollar }, bytes)

@[simp] theorem encode_length (message : AuctionInformationMessage) : (encode message).length = 79 := by
  simp [encode]

theorem encode_length_pos (message : AuctionInformationMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : AuctionInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end AuctionInformationMessage

/-- Any Message Data, selected by Message Type -/
inductive MessageData where
  | systemEventMessage (message : SystemEventMessage) -- 'S' 0x53
  | securityDirectoryMessage (message : SecurityDirectoryMessage) -- 'D' 0x44
  | tradingStatusMessage (message : TradingStatusMessage) -- 'H' 0x48
  | retailLiquidityIndicatorMessage (message : RetailLiquidityIndicatorMessage) -- 'I' 0x49
  | operationalHaltStatusMessage (message : OperationalHaltStatusMessage) -- 'O' 0x4F
  | shortSalePriceTestStatusMessage (message : ShortSalePriceTestStatusMessage) -- 'P' 0x50
  | quoteUpdateMessage (message : QuoteUpdateMessage) -- 'Q' 0x51
  | tradeReportMessage (message : TradeReportMessage) -- 'T' 0x54
  | officialPriceMessage (message : OfficialPriceMessage) -- 'X' 0x58
  | tradeBreakMessage (message : TradeBreakMessage) -- 'B' 0x42
  | auctionInformationMessage (message : AuctionInformationMessage) -- 'A' 0x41
  deriving DecidableEq, Repr

namespace MessageData

/-- The Message Type each message is sent under -/
def tag : MessageData → BitVec 8
  | .systemEventMessage _ => 83
  | .securityDirectoryMessage _ => 68
  | .tradingStatusMessage _ => 72
  | .retailLiquidityIndicatorMessage _ => 73
  | .operationalHaltStatusMessage _ => 79
  | .shortSalePriceTestStatusMessage _ => 80
  | .quoteUpdateMessage _ => 81
  | .tradeReportMessage _ => 84
  | .officialPriceMessage _ => 88
  | .tradeBreakMessage _ => 66
  | .auctionInformationMessage _ => 65

def encode : MessageData → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .securityDirectoryMessage message => SecurityDirectoryMessage.encode message
  | .tradingStatusMessage message => TradingStatusMessage.encode message
  | .retailLiquidityIndicatorMessage message => RetailLiquidityIndicatorMessage.encode message
  | .operationalHaltStatusMessage message => OperationalHaltStatusMessage.encode message
  | .shortSalePriceTestStatusMessage message => ShortSalePriceTestStatusMessage.encode message
  | .quoteUpdateMessage message => QuoteUpdateMessage.encode message
  | .tradeReportMessage message => TradeReportMessage.encode message
  | .officialPriceMessage message => OfficialPriceMessage.encode message
  | .tradeBreakMessage message => TradeBreakMessage.encode message
  | .auctionInformationMessage message => AuctionInformationMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (MessageData × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 68 then (SecurityDirectoryMessage.decode bytes).map fun (message, rest) => (.securityDirectoryMessage message, rest)
  else if tag = 72 then (TradingStatusMessage.decode bytes).map fun (message, rest) => (.tradingStatusMessage message, rest)
  else if tag = 73 then (RetailLiquidityIndicatorMessage.decode bytes).map fun (message, rest) => (.retailLiquidityIndicatorMessage message, rest)
  else if tag = 79 then (OperationalHaltStatusMessage.decode bytes).map fun (message, rest) => (.operationalHaltStatusMessage message, rest)
  else if tag = 80 then (ShortSalePriceTestStatusMessage.decode bytes).map fun (message, rest) => (.shortSalePriceTestStatusMessage message, rest)
  else if tag = 81 then (QuoteUpdateMessage.decode bytes).map fun (message, rest) => (.quoteUpdateMessage message, rest)
  else if tag = 84 then (TradeReportMessage.decode bytes).map fun (message, rest) => (.tradeReportMessage message, rest)
  else if tag = 88 then (OfficialPriceMessage.decode bytes).map fun (message, rest) => (.officialPriceMessage message, rest)
  else if tag = 66 then (TradeBreakMessage.decode bytes).map fun (message, rest) => (.tradeBreakMessage message, rest)
  else if tag = 65 then (AuctionInformationMessage.decode bytes).map fun (message, rest) => (.auctionInformationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageData) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageData

/-- Message -/
structure Message where
  messageData : MessageData
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  MessageType.encode (MessageData.tag message.messageData)
    ++ MessageData.encode message.messageData

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← MessageType.decode bytes
  let (messageData, bytes) ← MessageData.decode messageType bytes
  pure ({ messageData }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  simp [decodeBody, encodeBody, List.append_assoc]

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 65536 := by
  cases h : message.messageData with
  | systemEventMessage inner =>
    simp [encodeBody, h, MessageData.encode, SystemEventMessage.encode]
  | securityDirectoryMessage inner =>
    simp [encodeBody, h, MessageData.encode, SecurityDirectoryMessage.encode]
  | tradingStatusMessage inner =>
    simp [encodeBody, h, MessageData.encode, TradingStatusMessage.encode]
  | retailLiquidityIndicatorMessage inner =>
    simp [encodeBody, h, MessageData.encode, RetailLiquidityIndicatorMessage.encode]
  | operationalHaltStatusMessage inner =>
    simp [encodeBody, h, MessageData.encode, OperationalHaltStatusMessage.encode]
  | shortSalePriceTestStatusMessage inner =>
    simp [encodeBody, h, MessageData.encode, ShortSalePriceTestStatusMessage.encode]
  | quoteUpdateMessage inner =>
    simp [encodeBody, h, MessageData.encode, QuoteUpdateMessage.encode]
  | tradeReportMessage inner =>
    simp [encodeBody, h, MessageData.encode, TradeReportMessage.encode]
  | officialPriceMessage inner =>
    simp [encodeBody, h, MessageData.encode, OfficialPriceMessage.encode]
  | tradeBreakMessage inner =>
    simp [encodeBody, h, MessageData.encode, TradeBreakMessage.encode]
  | auctionInformationMessage inner =>
    simp [encodeBody, h, MessageData.encode, AuctionInformationMessage.encode]

/-- Size rule: Message Length counts the bytes after it, so it is written from the body -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 0 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  version : BitVec 8
  reserved : Alpha 1
  messageProtocolId : BitVec 16
  channelId : BitVec 32
  sessionId : BitVec 32
  payloadLength : BitVec 16
  streamOffset : BitVec 64
  firstMessageSequenceNumber : BitVec 64
  sendTime : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 1 message.version
    ++ Alpha.encode message.reserved
    ++ encodeUIntLE 2 message.messageProtocolId
    ++ encodeUIntLE 4 message.channelId
    ++ encodeUIntLE 4 message.sessionId
    ++ encodeUIntLE 2 message.payloadLength
    ++ encodeUIntLE 2 (BitVec.ofNat 16 message.message.val.length)
    ++ encodeUIntLE 8 message.streamOffset
    ++ encodeUIntLE 8 message.firstMessageSequenceNumber
    ++ encodeUIntLE 8 message.sendTime
    ++ encodeMany Message.encode message.message.val

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (version, bytes) ← decodeUIntLE 1 bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (messageProtocolId, bytes) ← decodeUIntLE 2 bytes
  let (channelId, bytes) ← decodeUIntLE 4 bytes
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (payloadLength, bytes) ← decodeUIntLE 2 bytes
  let (messageCount, bytes) ← decodeUIntLE 2 bytes
  let (streamOffset, bytes) ← decodeUIntLE 8 bytes
  let (firstMessageSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (sendTime, bytes) ← decodeUIntLE 8 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 65536 then
    pure ({ version, reserved, messageProtocolId, channelId, sessionId, payloadLength, streamOffset, firstMessageSequenceNumber, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_message : message.message.val.length < 65536 := by simpa using message.message.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_message, fits_message, decodeMany_encodeMany Message.encode Message.decode Message.decode_encode]

end Packet

end Omi.IexIexequitiesTopsIextpV166
