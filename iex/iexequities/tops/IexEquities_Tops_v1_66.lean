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

/-- System Event: one byte code -/
def SystemEvent.codes : List UInt8 :=
  [0x4F, 0x53, 0x52, 0x4D, 0x45, 0x43]

inductive SystemEvent where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfRegularMarketHours -- Start Of Regular Market Hours
  | endOfRegularMarketHours -- End Of Regular Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemEvent.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemEvent

def toByte : SystemEvent → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfRegularMarketHours => 0x52
  | .endOfRegularMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemEvent :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x52 then .startOfRegularMarketHours
  else if byte = 0x4D then .endOfRegularMarketHours
  else if byte = 0x45 then .endOfSystemHours
  else .endOfMessages

def ofByte (byte : UInt8) : SystemEvent :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemEvent) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfRegularMarketHours => decide
  | endOfRegularMarketHours => decide
  | endOfSystemHours => decide
  | endOfMessages => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SystemEvent) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SystemEvent × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SystemEvent) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SystemEvent) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SystemEvent

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x48, 0x4F, 0x50, 0x54]

inductive TradingStatus where
  | tradingHaltedAcrossAllUsEquityMarkets -- Trading Halted Across All Us Equity Markets
  | tradingHaltReleasedIntoAnOrderAcceptancePeriodOnIex -- Trading Halt Released Into An Order Acceptance Period On Iex
  | tradingPausedAndOrderAcceptancePeriodOnIex -- Trading Paused And Order Acceptance Period On Iex
  | tradingOnIex -- Trading On Iex
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .tradingHaltedAcrossAllUsEquityMarkets => 0x48
  | .tradingHaltReleasedIntoAnOrderAcceptancePeriodOnIex => 0x4F
  | .tradingPausedAndOrderAcceptancePeriodOnIex => 0x50
  | .tradingOnIex => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x48 then .tradingHaltedAcrossAllUsEquityMarkets
  else if byte = 0x4F then .tradingHaltReleasedIntoAnOrderAcceptancePeriodOnIex
  else if byte = 0x50 then .tradingPausedAndOrderAcceptancePeriodOnIex
  else .tradingOnIex

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | tradingHaltedAcrossAllUsEquityMarkets => decide
  | tradingHaltReleasedIntoAnOrderAcceptancePeriodOnIex => decide
  | tradingPausedAndOrderAcceptancePeriodOnIex => decide
  | tradingOnIex => decide
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

/-- Retail Liquidity Indicator: one byte code -/
def RetailLiquidityIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43]

inductive RetailLiquidityIndicator where
  | notApplicable -- Not Applicable
  | buyInterest -- Buy Interest
  | sellInterest -- Sell Interest
  | buyAndSellInterest -- Buy And Sell Interest
  | unlisted (byte : { byte : UInt8 // byte ∉ RetailLiquidityIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetailLiquidityIndicator

def toByte : RetailLiquidityIndicator → UInt8
  | .notApplicable => 0x20
  | .buyInterest => 0x41
  | .sellInterest => 0x42
  | .buyAndSellInterest => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RetailLiquidityIndicator :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x41 then .buyInterest
  else if byte = 0x42 then .sellInterest
  else .buyAndSellInterest

def ofByte (byte : UInt8) : RetailLiquidityIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetailLiquidityIndicator) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | buyInterest => decide
  | sellInterest => decide
  | buyAndSellInterest => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RetailLiquidityIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetailLiquidityIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RetailLiquidityIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RetailLiquidityIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RetailLiquidityIndicator

/-- Operational Halt Status: one byte code -/
def OperationalHaltStatus.codes : List UInt8 :=
  [0x4F, 0x4E]

inductive OperationalHaltStatus where
  | iexSpecificOperationalTradingHalt -- Iex Specific Operational Trading Halt
  | notOperationallyHaltedOnIex -- Not Operationally Halted On Iex
  | unlisted (byte : { byte : UInt8 // byte ∉ OperationalHaltStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OperationalHaltStatus

def toByte : OperationalHaltStatus → UInt8
  | .iexSpecificOperationalTradingHalt => 0x4F
  | .notOperationallyHaltedOnIex => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OperationalHaltStatus :=
  if byte = 0x4F then .iexSpecificOperationalTradingHalt
  else .notOperationallyHaltedOnIex

def ofByte (byte : UInt8) : OperationalHaltStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OperationalHaltStatus) : ofByte value.toByte = value := by
  cases value with
  | iexSpecificOperationalTradingHalt => decide
  | notOperationallyHaltedOnIex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OperationalHaltStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OperationalHaltStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OperationalHaltStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OperationalHaltStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OperationalHaltStatus

/-- Detail: one byte code -/
def Detail.codes : List UInt8 :=
  [0x20, 0x41, 0x43, 0x44, 0x4E]

inductive Detail where
  | noPriceTestInPlace -- No Price Test In Place
  | activated -- Activated
  | continued -- Continued
  | deactivated -- Deactivated
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ Detail.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Detail

def toByte : Detail → UInt8
  | .noPriceTestInPlace => 0x20
  | .activated => 0x41
  | .continued => 0x43
  | .deactivated => 0x44
  | .notAvailable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Detail :=
  if byte = 0x20 then .noPriceTestInPlace
  else if byte = 0x41 then .activated
  else if byte = 0x43 then .continued
  else if byte = 0x44 then .deactivated
  else .notAvailable

def ofByte (byte : UInt8) : Detail :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Detail) : ofByte value.toByte = value := by
  cases value with
  | noPriceTestInPlace => decide
  | activated => decide
  | continued => decide
  | deactivated => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Detail) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Detail × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Detail) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Detail) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Detail

/-- Price Type: one byte code -/
def PriceType.codes : List UInt8 :=
  [0x51, 0x4D]

inductive PriceType where
  | iexOfficialOpeningPrice -- Iex Official Opening Price
  | iexOfficialClosingPrice -- Iex Official Closing Price
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceType

def toByte : PriceType → UInt8
  | .iexOfficialOpeningPrice => 0x51
  | .iexOfficialClosingPrice => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceType :=
  if byte = 0x51 then .iexOfficialOpeningPrice
  else .iexOfficialClosingPrice

def ofByte (byte : UInt8) : PriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceType) : ofByte value.toByte = value := by
  cases value with
  | iexOfficialOpeningPrice => decide
  | iexOfficialClosingPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceType

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x4F, 0x43, 0x49, 0x48, 0x56]

inductive AuctionType where
  | openingAuction -- Opening Auction
  | closingAuction -- Closing Auction
  | ipoAuction -- Ipo Auction
  | haltAuction -- Halt Auction
  | volatilityAuction -- Volatility Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .openingAuction => 0x4F
  | .closingAuction => 0x43
  | .ipoAuction => 0x49
  | .haltAuction => 0x48
  | .volatilityAuction => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x4F then .openingAuction
  else if byte = 0x43 then .closingAuction
  else if byte = 0x49 then .ipoAuction
  else if byte = 0x48 then .haltAuction
  else .volatilityAuction

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | openingAuction => decide
  | closingAuction => decide
  | ipoAuction => decide
  | haltAuction => decide
  | volatilityAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AuctionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionType

/-- Imbalance Side: one byte code -/
def ImbalanceSide.codes : List UInt8 :=
  [0x42, 0x53, 0x4E]

inductive ImbalanceSide where
  | buy -- Buy
  | sell -- Sell
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceSide

def toByte : ImbalanceSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .none_ => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .none_

def ofByte (byte : UInt8) : ImbalanceSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | none_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ImbalanceSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ImbalanceSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

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
  unfold encode
  simp only [List.length_append, SystemEvent.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [SystemEvent.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, TradingStatus.encode_length, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradingStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [TradingStatus.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, RetailLiquidityIndicator.encode_length, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RetailLiquidityIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetailLiquidityIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [RetailLiquidityIndicator.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, OperationalHaltStatus.encode_length, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OperationalHaltStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OperationalHaltStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [OperationalHaltStatus.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length, Alpha.encode_length, Detail.encode_length]

theorem encode_length_pos (message : ShortSalePriceTestStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortSalePriceTestStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Detail.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, PriceType.encode_length, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OfficialPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OfficialPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [PriceType.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeBreakMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBreakMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, AuctionType.encode_length, encodeUIntLE_length, Alpha.encode_length, ImbalanceSide.encode_length]

theorem encode_length_pos (message : AuctionInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [AuctionType.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [ImbalanceSide.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

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
  encodeUInt 1 (MessageData.tag message.messageData)
    ++ MessageData.encode message.messageData

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (messageData, bytes) ← MessageData.decode messageType bytes
  pure ({ messageData }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [MessageData.decode_encode, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.messageData with
  | systemEventMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | securityDirectoryMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, SecurityDirectoryMessage.encode_length]
    omega
  | tradingStatusMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, TradingStatusMessage.encode_length]
    omega
  | retailLiquidityIndicatorMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, RetailLiquidityIndicatorMessage.encode_length]
    omega
  | operationalHaltStatusMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, OperationalHaltStatusMessage.encode_length]
    omega
  | shortSalePriceTestStatusMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, ShortSalePriceTestStatusMessage.encode_length]
    omega
  | quoteUpdateMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, QuoteUpdateMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, TradeReportMessage.encode_length]
    omega
  | officialPriceMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, OfficialPriceMessage.encode_length]
    omega
  | tradeBreakMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, TradeBreakMessage.encode_length]
    omega
  | auctionInformationMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, AuctionInformationMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
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
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.message.val.length)
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
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ version, reserved, messageProtocolId, channelId, sessionId, payloadLength, streamOffset, firstMessageSequenceNumber, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, Option.bind_some]
  dsimp only
  simp only [message.message.length_lt, ↓reduceDIte]
  rfl

end Packet

end Omi.IexIexequitiesTopsIextpV166
