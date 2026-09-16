import Omi.Wire

/-!
# Investors Exchange DeepPlus v1.01

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: Security Directory Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Modify Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Sale Condition Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.IexIexequitiesDeepplusIextpV101

/-- Message Type: one byte code -/
inductive MessageType where
  | systemEventMessage -- System Event Message
  | securityDirectoryMessage -- Security Directory Message
  | tradingStatusMessage -- Trading Status Message
  | retailLiquidityIndicatorMessage -- Retail Liquidity Indicator Message
  | operationalHaltStatusMessage -- Operational Halt Status Message
  | shortSalePriceTestStatusMessage -- Short Sale Price Test Status Message
  | securityEventMessage -- Security Event Message
  | addOrderMessage -- Add Order Message
  | orderModifyMessage -- Order Modify Message
  | orderDeleteMessage -- Order Delete Message
  | orderExecutedMessage -- Order Executed Message
  | tradeMessage -- Trade Message
  | tradeBreakMessage -- Trade Break Message
  | clearBookMessage -- Clear Book Message
  deriving DecidableEq, Repr

namespace MessageType

def toByte : MessageType → UInt8
  | .systemEventMessage => 0x53
  | .securityDirectoryMessage => 0x44
  | .tradingStatusMessage => 0x48
  | .retailLiquidityIndicatorMessage => 0x49
  | .operationalHaltStatusMessage => 0x4F
  | .shortSalePriceTestStatusMessage => 0x50
  | .securityEventMessage => 0x45
  | .addOrderMessage => 0x61
  | .orderModifyMessage => 0x4D
  | .orderDeleteMessage => 0x52
  | .orderExecutedMessage => 0x4C
  | .tradeMessage => 0x54
  | .tradeBreakMessage => 0x42
  | .clearBookMessage => 0x43

def ofByte? (byte : UInt8) : Option MessageType :=
  if byte = 0x53 then some .systemEventMessage
  else if byte = 0x44 then some .securityDirectoryMessage
  else if byte = 0x48 then some .tradingStatusMessage
  else if byte = 0x49 then some .retailLiquidityIndicatorMessage
  else if byte = 0x4F then some .operationalHaltStatusMessage
  else if byte = 0x50 then some .shortSalePriceTestStatusMessage
  else if byte = 0x45 then some .securityEventMessage
  else if byte = 0x61 then some .addOrderMessage
  else if byte = 0x4D then some .orderModifyMessage
  else if byte = 0x52 then some .orderDeleteMessage
  else if byte = 0x4C then some .orderExecutedMessage
  else if byte = 0x54 then some .tradeMessage
  else if byte = 0x42 then some .tradeBreakMessage
  else if byte = 0x43 then some .clearBookMessage
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
  | shortSalePriceTestRestrictionInEffectDueToAnIntradayPriceDropInTheSecurity -- Short Sale Price Test Restriction In Effect Due To An Intraday Price Drop In The Security
  | shortSalePriceTestRestrictionRemainsInEffectFromPriorDay -- Short Sale Price Test Restriction Remains In Effect From Prior Day
  | shortSalePriceTestRestrictionDeactivated -- Short Sale Price Test Restriction Deactivated
  | notAvailable -- Not Available
  deriving DecidableEq, Repr

namespace Detail

def toByte : Detail → UInt8
  | .noPriceTestInPlace => 0x20
  | .shortSalePriceTestRestrictionInEffectDueToAnIntradayPriceDropInTheSecurity => 0x41
  | .shortSalePriceTestRestrictionRemainsInEffectFromPriorDay => 0x43
  | .shortSalePriceTestRestrictionDeactivated => 0x44
  | .notAvailable => 0x4E

def ofByte? (byte : UInt8) : Option Detail :=
  if byte = 0x20 then some .noPriceTestInPlace
  else if byte = 0x41 then some .shortSalePriceTestRestrictionInEffectDueToAnIntradayPriceDropInTheSecurity
  else if byte = 0x43 then some .shortSalePriceTestRestrictionRemainsInEffectFromPriorDay
  else if byte = 0x44 then some .shortSalePriceTestRestrictionDeactivated
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

/-- Security Event: one byte code -/
inductive SecurityEvent where
  | openingProcessComplete -- Opening Process Complete
  | closingProcessComplete -- Closing Process Complete
  deriving DecidableEq, Repr

namespace SecurityEvent

def toByte : SecurityEvent → UInt8
  | .openingProcessComplete => 0x4F
  | .closingProcessComplete => 0x43

def ofByte? (byte : UInt8) : Option SecurityEvent :=
  if byte = 0x4F then some .openingProcessComplete
  else if byte = 0x43 then some .closingProcessComplete
  else none

theorem ofByte?_toByte (value : SecurityEvent) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : SecurityEvent) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityEvent × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityEvent) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityEvent) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end SecurityEvent

/-- Side: one byte code -/
inductive Side where
  | buy -- Buy
  | sell -- Sell
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x38
  | .sell => 0x35

def ofByte? (byte : UInt8) : Option Side :=
  if byte = 0x38 then some .buy
  else if byte = 0x35 then some .sell
  else none

theorem ofByte?_toByte (value : Side) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end Side

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

/-- Security Event Message: 17 bytes -/
structure SecurityEventMessage where
  securityEvent : SecurityEvent
  timestamp : BitVec 64
  symbol : Alpha 8
  deriving DecidableEq, Repr

namespace SecurityEventMessage

def encode (message : SecurityEventMessage) : List UInt8 :=
  SecurityEvent.encode message.securityEvent
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol

def decode (bytes : List UInt8) : Option (SecurityEventMessage × List UInt8) := do
  let (securityEvent, bytes) ← SecurityEvent.decode bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  pure ({ securityEvent, timestamp, symbol }, bytes)

@[simp] theorem encode_length (message : SecurityEventMessage) : (encode message).length = 17 := by
  simp [encode]

theorem encode_length_pos (message : SecurityEventMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SecurityEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end SecurityEventMessage

/-- Add Order Message: 37 bytes -/
structure AddOrderMessage where
  side : Side
  timestamp : BitVec 64
  symbol : Alpha 8
  orderId : BitVec 64
  size : BitVec 32
  price : BitVec 64
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  Side.encode message.side
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 4 message.size
    ++ encodeUIntLE 8 message.price

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (side, bytes) ← Side.decode bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ side, timestamp, symbol, orderId, size, price }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 37 := by
  simp [encode]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end AddOrderMessage

/-- Order Modify Message: 37 bytes -/
structure OrderModifyMessage where
  modifyFlags : BitVec 8
  timestamp : BitVec 64
  symbol : Alpha 8
  orderIdReference : BitVec 64
  size : BitVec 32
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderModifyMessage

def encode (message : OrderModifyMessage) : List UInt8 :=
  encodeUIntLE 1 message.modifyFlags
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.orderIdReference
    ++ encodeUIntLE 4 message.size
    ++ encodeUIntLE 8 message.price

def decode (bytes : List UInt8) : Option (OrderModifyMessage × List UInt8) := do
  let (modifyFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (orderIdReference, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ modifyFlags, timestamp, symbol, orderIdReference, size, price }, bytes)

@[simp] theorem encode_length (message : OrderModifyMessage) : (encode message).length = 37 := by
  simp [encode]

theorem encode_length_pos (message : OrderModifyMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : OrderModifyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end OrderModifyMessage

/-- Order Delete Message: 25 bytes -/
structure OrderDeleteMessage where
  reserved1 : Alpha 1
  timestamp : BitVec 64
  symbol : Alpha 8
  orderIdReference : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.orderIdReference

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (orderIdReference, bytes) ← decodeUIntLE 8 bytes
  pure ({ reserved1, timestamp, symbol, orderIdReference }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 25 := by
  simp [encode]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end OrderDeleteMessage

/-- Order Executed Message: 45 bytes -/
structure OrderExecutedMessage where
  saleConditionFlags : BitVec 8
  timestamp : BitVec 64
  symbol : Alpha 8
  orderIdReference : BitVec 64
  size : BitVec 32
  price : BitVec 64
  tradeId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUIntLE 1 message.saleConditionFlags
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.orderIdReference
    ++ encodeUIntLE 4 message.size
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.tradeId

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (saleConditionFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (orderIdReference, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  pure ({ saleConditionFlags, timestamp, symbol, orderIdReference, size, price, tradeId }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 45 := by
  simp [encode]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end OrderExecutedMessage

/-- Trade Message: 37 bytes -/
structure TradeMessage where
  saleConditionFlags : BitVec 8
  timestamp : BitVec 64
  symbol : Alpha 8
  size : BitVec 32
  price : BitVec 64
  tradeId : BitVec 64
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 1 message.saleConditionFlags
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 4 message.size
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.tradeId

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (saleConditionFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  pure ({ saleConditionFlags, timestamp, symbol, size, price, tradeId }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 37 := by
  simp [encode]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end TradeMessage

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

/-- Clear Book Message: 17 bytes -/
structure ClearBookMessage where
  reserved1 : Alpha 1
  timestamp : BitVec 64
  symbol : Alpha 8
  deriving DecidableEq, Repr

namespace ClearBookMessage

def encode (message : ClearBookMessage) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ encodeUIntLE 8 message.timestamp
    ++ Alpha.encode message.symbol

def decode (bytes : List UInt8) : Option (ClearBookMessage × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  pure ({ reserved1, timestamp, symbol }, bytes)

@[simp] theorem encode_length (message : ClearBookMessage) : (encode message).length = 17 := by
  simp [encode]

theorem encode_length_pos (message : ClearBookMessage) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClearBookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end ClearBookMessage

/-- Any Message Data, selected by Message Type -/
inductive MessageData where
  | systemEventMessage (message : SystemEventMessage) -- 'S' 0x53
  | securityDirectoryMessage (message : SecurityDirectoryMessage) -- 'D' 0x44
  | tradingStatusMessage (message : TradingStatusMessage) -- 'H' 0x48
  | retailLiquidityIndicatorMessage (message : RetailLiquidityIndicatorMessage) -- 'I' 0x49
  | operationalHaltStatusMessage (message : OperationalHaltStatusMessage) -- 'O' 0x4F
  | shortSalePriceTestStatusMessage (message : ShortSalePriceTestStatusMessage) -- 'P' 0x50
  | securityEventMessage (message : SecurityEventMessage) -- 'E' 0x45
  | addOrderMessage (message : AddOrderMessage) -- 'a' 0x61
  | orderModifyMessage (message : OrderModifyMessage) -- 'M' 0x4D
  | orderDeleteMessage (message : OrderDeleteMessage) -- 'R' 0x52
  | orderExecutedMessage (message : OrderExecutedMessage) -- 'L' 0x4C
  | tradeMessage (message : TradeMessage) -- 'T' 0x54
  | tradeBreakMessage (message : TradeBreakMessage) -- 'B' 0x42
  | clearBookMessage (message : ClearBookMessage) -- 'C' 0x43
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
  | .securityEventMessage _ => 69
  | .addOrderMessage _ => 97
  | .orderModifyMessage _ => 77
  | .orderDeleteMessage _ => 82
  | .orderExecutedMessage _ => 76
  | .tradeMessage _ => 84
  | .tradeBreakMessage _ => 66
  | .clearBookMessage _ => 67

def encode : MessageData → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .securityDirectoryMessage message => SecurityDirectoryMessage.encode message
  | .tradingStatusMessage message => TradingStatusMessage.encode message
  | .retailLiquidityIndicatorMessage message => RetailLiquidityIndicatorMessage.encode message
  | .operationalHaltStatusMessage message => OperationalHaltStatusMessage.encode message
  | .shortSalePriceTestStatusMessage message => ShortSalePriceTestStatusMessage.encode message
  | .securityEventMessage message => SecurityEventMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .orderModifyMessage message => OrderModifyMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .tradeBreakMessage message => TradeBreakMessage.encode message
  | .clearBookMessage message => ClearBookMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (MessageData × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 68 then (SecurityDirectoryMessage.decode bytes).map fun (message, rest) => (.securityDirectoryMessage message, rest)
  else if tag = 72 then (TradingStatusMessage.decode bytes).map fun (message, rest) => (.tradingStatusMessage message, rest)
  else if tag = 73 then (RetailLiquidityIndicatorMessage.decode bytes).map fun (message, rest) => (.retailLiquidityIndicatorMessage message, rest)
  else if tag = 79 then (OperationalHaltStatusMessage.decode bytes).map fun (message, rest) => (.operationalHaltStatusMessage message, rest)
  else if tag = 80 then (ShortSalePriceTestStatusMessage.decode bytes).map fun (message, rest) => (.shortSalePriceTestStatusMessage message, rest)
  else if tag = 69 then (SecurityEventMessage.decode bytes).map fun (message, rest) => (.securityEventMessage message, rest)
  else if tag = 97 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 77 then (OrderModifyMessage.decode bytes).map fun (message, rest) => (.orderModifyMessage message, rest)
  else if tag = 82 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 76 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 84 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 66 then (TradeBreakMessage.decode bytes).map fun (message, rest) => (.tradeBreakMessage message, rest)
  else if tag = 67 then (ClearBookMessage.decode bytes).map fun (message, rest) => (.clearBookMessage message, rest)
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
  | securityEventMessage inner =>
    simp [encodeBody, h, MessageData.encode, SecurityEventMessage.encode]
  | addOrderMessage inner =>
    simp [encodeBody, h, MessageData.encode, AddOrderMessage.encode]
  | orderModifyMessage inner =>
    simp [encodeBody, h, MessageData.encode, OrderModifyMessage.encode]
  | orderDeleteMessage inner =>
    simp [encodeBody, h, MessageData.encode, OrderDeleteMessage.encode]
  | orderExecutedMessage inner =>
    simp [encodeBody, h, MessageData.encode, OrderExecutedMessage.encode]
  | tradeMessage inner =>
    simp [encodeBody, h, MessageData.encode, TradeMessage.encode]
  | tradeBreakMessage inner =>
    simp [encodeBody, h, MessageData.encode, TradeBreakMessage.encode]
  | clearBookMessage inner =>
    simp [encodeBody, h, MessageData.encode, ClearBookMessage.encode]

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

end Omi.IexIexequitiesDeepplusIextpV101
