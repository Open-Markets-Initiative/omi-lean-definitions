import Omi.Wire

/-!
# Bolsa Institucional de Valores Total View v1.12

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BivaBivaequitiesTotalviewItchV112

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4D, 0x56, 0x55, 0x50, 0x54, 0x45, 0x43]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfMarketHours -- Start Of Market Hours
  | endOfMarketHours -- End Of Market Hours
  | scheduledAuctionStarts -- Scheduled Auction Starts
  | scheduledAuctionCloses -- Scheduled Auction Closes
  | startOfPostCloseSession -- Start Of Post Close Session
  | endOfPostCloseSession -- End Of Post Close Session
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfMarketHours => 0x51
  | .endOfMarketHours => 0x4D
  | .scheduledAuctionStarts => 0x56
  | .scheduledAuctionCloses => 0x55
  | .startOfPostCloseSession => 0x50
  | .endOfPostCloseSession => 0x54
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x56 then .scheduledAuctionStarts
  else if byte = 0x55 then .scheduledAuctionCloses
  else if byte = 0x50 then .startOfPostCloseSession
  else if byte = 0x54 then .endOfPostCloseSession
  else if byte = 0x45 then .endOfSystemHours
  else .endOfMessages

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfMarketHours => decide
  | endOfMarketHours => decide
  | scheduledAuctionStarts => decide
  | scheduledAuctionCloses => decide
  | startOfPostCloseSession => decide
  | endOfPostCloseSession => decide
  | endOfSystemHours => decide
  | endOfMessages => decide
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

/-- Listing Type: one byte code -/
def ListingType.codes : List UInt8 :=
  [0x52, 0x53]

inductive ListingType where
  | regularSecurities -- Regular Securities
  | subRmSecurities -- Sub Rm Securities
  | unlisted (byte : { byte : UInt8 // byte ∉ ListingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListingType

def toByte : ListingType → UInt8
  | .regularSecurities => 0x52
  | .subRmSecurities => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListingType :=
  if byte = 0x52 then .regularSecurities
  else .subRmSecurities

def ofByte (byte : UInt8) : ListingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListingType) : ofByte value.toByte = value := by
  cases value with
  | regularSecurities => decide
  | subRmSecurities => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ListingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ListingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ListingType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ListingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ListingType

/-- Trading State: one byte code -/
def TradingState.codes : List UInt8 :=
  [0x54, 0x56]

inductive TradingState where
  | trading -- Trading
  | suspended -- Suspended
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .trading => 0x54
  | .suspended => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x54 then .trading
  else .suspended

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | trading => decide
  | suspended => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingState

/-- Trading Action Reason: one byte code -/
def TradingActionReason.codes : List UInt8 :=
  [0x4E, 0x48, 0x41, 0x42, 0x51, 0x53, 0x4D, 0x4F, 0x43, 0x49, 0x45, 0x4C]

inductive TradingActionReason where
  | normalTrading -- Normal Trading
  | volatilityAuction -- Volatility Auction
  | continuousAuctionStart -- Continuous Auction Start
  | continuousAuctionEnd -- Continuous Auction End
  | newsPending -- News Pending
  | staticPriceBandBreach -- Static Price Band Breach
  | marketSurveillanceSuspension -- Market Surveillance Suspension
  | suspensionByMarketOfOrigin -- Suspension By Market Of Origin
  | nonCompliance -- Non Compliance
  | startOfIndicationOfInterest -- Start Of Indication Of Interest
  | expiredSecurityIsUnavailableForTrading -- Expired Security Is Unavailable For Trading
  | notYetAvailableForTrading -- Not Yet Available For Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingActionReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingActionReason

def toByte : TradingActionReason → UInt8
  | .normalTrading => 0x4E
  | .volatilityAuction => 0x48
  | .continuousAuctionStart => 0x41
  | .continuousAuctionEnd => 0x42
  | .newsPending => 0x51
  | .staticPriceBandBreach => 0x53
  | .marketSurveillanceSuspension => 0x4D
  | .suspensionByMarketOfOrigin => 0x4F
  | .nonCompliance => 0x43
  | .startOfIndicationOfInterest => 0x49
  | .expiredSecurityIsUnavailableForTrading => 0x45
  | .notYetAvailableForTrading => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingActionReason :=
  if byte = 0x4E then .normalTrading
  else if byte = 0x48 then .volatilityAuction
  else if byte = 0x41 then .continuousAuctionStart
  else if byte = 0x42 then .continuousAuctionEnd
  else if byte = 0x51 then .newsPending
  else if byte = 0x53 then .staticPriceBandBreach
  else if byte = 0x4D then .marketSurveillanceSuspension
  else if byte = 0x4F then .suspensionByMarketOfOrigin
  else if byte = 0x43 then .nonCompliance
  else if byte = 0x49 then .startOfIndicationOfInterest
  else if byte = 0x45 then .expiredSecurityIsUnavailableForTrading
  else .notYetAvailableForTrading

def ofByte (byte : UInt8) : TradingActionReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingActionReason) : ofByte value.toByte = value := by
  cases value with
  | normalTrading => decide
  | volatilityAuction => decide
  | continuousAuctionStart => decide
  | continuousAuctionEnd => decide
  | newsPending => decide
  | staticPriceBandBreach => decide
  | marketSurveillanceSuspension => decide
  | suspensionByMarketOfOrigin => decide
  | nonCompliance => decide
  | startOfIndicationOfInterest => decide
  | expiredSecurityIsUnavailableForTrading => decide
  | notYetAvailableForTrading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingActionReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingActionReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingActionReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingActionReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingActionReason

/-- Price Type: one byte code -/
def PriceType.codes : List UInt8 :=
  [0x43, 0x52, 0x49, 0x56]

inductive PriceType where
  | closePrice -- Close Price
  | referencePrice -- Reference Price
  | inav -- Inav
  | vwapOrPpp -- Vwap Or Ppp
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceType

def toByte : PriceType → UInt8
  | .closePrice => 0x43
  | .referencePrice => 0x52
  | .inav => 0x49
  | .vwapOrPpp => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceType :=
  if byte = 0x43 then .closePrice
  else if byte = 0x52 then .referencePrice
  else if byte = 0x49 then .inav
  else .vwapOrPpp

def ofByte (byte : UInt8) : PriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceType) : ofByte value.toByte = value := by
  cases value with
  | closePrice => decide
  | referencePrice => decide
  | inav => decide
  | vwapOrPpp => decide
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

/-- Reference Price Reason: one byte code -/
def ReferencePriceReason.codes : List UInt8 :=
  [0x20]

inductive ReferencePriceReason where
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ ReferencePriceReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReferencePriceReason

def toByte : ReferencePriceReason → UInt8
  | .none_ => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ReferencePriceReason :=
  .none_

def ofByte (byte : UInt8) : ReferencePriceReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReferencePriceReason) : ofByte value.toByte = value := by
  cases value with
  | none_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReferencePriceReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReferencePriceReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReferencePriceReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReferencePriceReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReferencePriceReason

/-- Order Verb: one byte code -/
def OrderVerb.codes : List UInt8 :=
  [0x42, 0x53]

inductive OrderVerb where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderVerb.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderVerb

def toByte : OrderVerb → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderVerb :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : OrderVerb :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderVerb) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderVerb) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderVerb × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderVerb) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderVerb) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderVerb

/-- Trade Indicator: one byte code -/
def TradeIndicator.codes : List UInt8 :=
  [0x43, 0x45, 0x49, 0x52, 0x55]

inductive TradeIndicator where
  | intentionalCrossTrade -- Intentional Cross Trade
  | exceptionalCrossTradeAtVwap -- Exceptional Cross Trade At Vwap
  | ipoCross -- Ipo Cross
  | regularTrade -- Regular Trade
  | unintentionalSelfcross -- Unintentional Selfcross
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeIndicator

def toByte : TradeIndicator → UInt8
  | .intentionalCrossTrade => 0x43
  | .exceptionalCrossTradeAtVwap => 0x45
  | .ipoCross => 0x49
  | .regularTrade => 0x52
  | .unintentionalSelfcross => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeIndicator :=
  if byte = 0x43 then .intentionalCrossTrade
  else if byte = 0x45 then .exceptionalCrossTradeAtVwap
  else if byte = 0x49 then .ipoCross
  else if byte = 0x52 then .regularTrade
  else .unintentionalSelfcross

def ofByte (byte : UInt8) : TradeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeIndicator) : ofByte value.toByte = value := by
  cases value with
  | intentionalCrossTrade => decide
  | exceptionalCrossTradeAtVwap => decide
  | ipoCross => decide
  | regularTrade => decide
  | unintentionalSelfcross => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeIndicator

/-- Stat Update: one byte code -/
def StatUpdate.codes : List UInt8 :=
  [0x41, 0x56, 0x4C, 0x43, 0x4E]

inductive StatUpdate where
  | allStats -- All Stats
  | lastTradedPriceAndVolume -- Last Traded Price And Volume
  | lastTradedPriceOnly -- Last Traded Price Only
  | volumeOnly -- Volume Only
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ StatUpdate.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StatUpdate

def toByte : StatUpdate → UInt8
  | .allStats => 0x41
  | .lastTradedPriceAndVolume => 0x56
  | .lastTradedPriceOnly => 0x4C
  | .volumeOnly => 0x43
  | .none_ => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StatUpdate :=
  if byte = 0x41 then .allStats
  else if byte = 0x56 then .lastTradedPriceAndVolume
  else if byte = 0x4C then .lastTradedPriceOnly
  else if byte = 0x43 then .volumeOnly
  else .none_

def ofByte (byte : UInt8) : StatUpdate :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StatUpdate) : ofByte value.toByte = value := by
  cases value with
  | allStats => decide
  | lastTradedPriceAndVolume => decide
  | lastTradedPriceOnly => decide
  | volumeOnly => decide
  | none_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StatUpdate) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StatUpdate × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StatUpdate) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StatUpdate) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StatUpdate

/-- Printable: one byte code -/
def Printable.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Printable where
  | nonPrintable -- Non Printable
  | printable -- Printable
  | unlisted (byte : { byte : UInt8 // byte ∉ Printable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Printable

def toByte : Printable → UInt8
  | .nonPrintable => 0x4E
  | .printable => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Printable :=
  if byte = 0x4E then .nonPrintable
  else .printable

def ofByte (byte : UInt8) : Printable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Printable) : ofByte value.toByte = value := by
  cases value with
  | nonPrintable => decide
  | printable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Printable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Printable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Printable) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Printable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Printable

/-- Broken Trade Reason: one byte code -/
def BrokenTradeReason.codes : List UInt8 :=
  [0x53]

inductive BrokenTradeReason where
  | supervisory -- Supervisory
  | unlisted (byte : { byte : UInt8 // byte ∉ BrokenTradeReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BrokenTradeReason

def toByte : BrokenTradeReason → UInt8
  | .supervisory => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : BrokenTradeReason :=
  .supervisory

def ofByte (byte : UInt8) : BrokenTradeReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BrokenTradeReason) : ofByte value.toByte = value := by
  cases value with
  | supervisory => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BrokenTradeReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BrokenTradeReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BrokenTradeReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BrokenTradeReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BrokenTradeReason

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x4F, 0x49]

inductive CrossType where
  | preopeningSession -- Preopening Session
  | intradayAuction -- Intraday Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .preopeningSession => 0x4F
  | .intradayAuction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4F then .preopeningSession
  else .intradayAuction

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | preopeningSession => decide
  | intradayAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CrossType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossType

/-- Time Stamp Seconds Message: 4 bytes -/
structure TimeStampSecondsMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace TimeStampSecondsMessage

def encode (message : TimeStampSecondsMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (TimeStampSecondsMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : TimeStampSecondsMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : TimeStampSecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimeStampSecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TimeStampSecondsMessage

/-- System Event Message: 17 bytes -/
structure SystemEventMessage where
  nanoseconds : BitVec 32
  group : Alpha 8
  eventCode : EventCode
  orderbook : BitVec 32
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.group
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 4 message.orderbook)))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, group, eventCode, orderbook }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Price Tick Size Message: 16 bytes -/
structure PriceTickSizeMessage where
  nanoseconds : BitVec 32
  tickSizeTableId : BitVec 32
  priceTickSize : BitVec 32
  priceStart : BitVec 32
  deriving DecidableEq, Repr

namespace PriceTickSizeMessage

def encode (message : PriceTickSizeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.tickSizeTableId
    ++ (encodeUInt 4 message.priceTickSize
    ++ (encodeUInt 4 message.priceStart)))

def decode (bytes : List UInt8) : Option (PriceTickSizeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (priceTickSize, bytes) ← decodeUInt 4 bytes
  let (priceStart, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tickSizeTableId, priceTickSize, priceStart }, bytes)

@[simp] theorem encode_length (message : PriceTickSizeMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PriceTickSizeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceTickSizeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriceTickSizeMessage

/-- Quantity Tick Size Message: 24 bytes -/
structure QuantityTickSizeMessage where
  nanoseconds : BitVec 32
  tickSizeTableId : BitVec 32
  quantityTickSize : BitVec 64
  quantityStart : BitVec 64
  deriving DecidableEq, Repr

namespace QuantityTickSizeMessage

def encode (message : QuantityTickSizeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.tickSizeTableId
    ++ (encodeUInt 8 message.quantityTickSize
    ++ (encodeUInt 8 message.quantityStart)))

def decode (bytes : List UInt8) : Option (QuantityTickSizeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (quantityTickSize, bytes) ← decodeUInt 8 bytes
  let (quantityStart, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tickSizeTableId, quantityTickSize, quantityStart }, bytes)

@[simp] theorem encode_length (message : QuantityTickSizeMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : QuantityTickSizeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuantityTickSizeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuantityTickSizeMessage

/-- Orderbook Directory Message: 99 bytes -/
structure OrderbookDirectoryMessage where
  nanoseconds : BitVec 32
  orderbook : BitVec 32
  isin : Alpha 12
  secCode : Alpha 15
  currency : Alpha 3
  group : Alpha 8
  minimumQuantity : BitVec 64
  quantityTickSizeTableId : BitVec 32
  quantityDecimals : BitVec 32
  priceTickSizeTableId : BitVec 32
  priceDecimals : BitVec 32
  delistingOrMaturityDate : BitVec 32
  delistingTime : BitVec 32
  turnoverRatio : Alpha 1
  quotationBasis : Alpha 3
  instrument : Alpha 12
  listingType : ListingType
  listingExchange : Alpha 4
  deriving DecidableEq, Repr

namespace OrderbookDirectoryMessage

def encode (message : OrderbookDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderbook
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.secCode
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.group
    ++ (encodeUInt 8 message.minimumQuantity
    ++ (encodeUInt 4 message.quantityTickSizeTableId
    ++ (encodeUInt 4 message.quantityDecimals
    ++ (encodeUInt 4 message.priceTickSizeTableId
    ++ (encodeUInt 4 message.priceDecimals
    ++ (encodeUInt 4 message.delistingOrMaturityDate
    ++ (encodeUInt 4 message.delistingTime
    ++ (Alpha.encode message.turnoverRatio
    ++ (Alpha.encode message.quotationBasis
    ++ (Alpha.encode message.instrument
    ++ (ListingType.encode message.listingType
    ++ (Alpha.encode message.listingExchange)))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderbookDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (secCode, bytes) ← Alpha.decode 15 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  let (minimumQuantity, bytes) ← decodeUInt 8 bytes
  let (quantityTickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (quantityDecimals, bytes) ← decodeUInt 4 bytes
  let (priceTickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (priceDecimals, bytes) ← decodeUInt 4 bytes
  let (delistingOrMaturityDate, bytes) ← decodeUInt 4 bytes
  let (delistingTime, bytes) ← decodeUInt 4 bytes
  let (turnoverRatio, bytes) ← Alpha.decode 1 bytes
  let (quotationBasis, bytes) ← Alpha.decode 3 bytes
  let (instrument, bytes) ← Alpha.decode 12 bytes
  let (listingType, bytes) ← ListingType.decode bytes
  let (listingExchange, bytes) ← Alpha.decode 4 bytes
  pure ({ nanoseconds, orderbook, isin, secCode, currency, group, minimumQuantity, quantityTickSizeTableId, quantityDecimals, priceTickSizeTableId, priceDecimals, delistingOrMaturityDate, delistingTime, turnoverRatio, quotationBasis, instrument, listingType, listingExchange }, bytes)

@[simp] theorem encode_length (message : OrderbookDirectoryMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ListingType.encode_length]

theorem encode_length_pos (message : OrderbookDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookDirectoryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ListingType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderbookDirectoryMessage

/-- Participant Directory Message: 20 bytes -/
structure ParticipantDirectoryMessage where
  nanoseconds : BitVec 32
  participantId : BitVec 32
  participantCode : Alpha 12
  deriving DecidableEq, Repr

namespace ParticipantDirectoryMessage

def encode (message : ParticipantDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.participantId
    ++ (Alpha.encode message.participantCode))

def decode (bytes : List UInt8) : Option (ParticipantDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (participantId, bytes) ← decodeUInt 4 bytes
  let (participantCode, bytes) ← Alpha.decode 12 bytes
  pure ({ nanoseconds, participantId, participantCode }, bytes)

@[simp] theorem encode_length (message : ParticipantDirectoryMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ParticipantDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ParticipantDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ParticipantDirectoryMessage

/-- Orderbook Trading Action Message: 10 bytes -/
structure OrderbookTradingActionMessage where
  nanoseconds : BitVec 32
  orderbook : BitVec 32
  tradingState : TradingState
  tradingActionReason : TradingActionReason
  deriving DecidableEq, Repr

namespace OrderbookTradingActionMessage

def encode (message : OrderbookTradingActionMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderbook
    ++ (TradingState.encode message.tradingState
    ++ (TradingActionReason.encode message.tradingActionReason)))

def decode (bytes : List UInt8) : Option (OrderbookTradingActionMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  let (tradingActionReason, bytes) ← TradingActionReason.decode bytes
  pure ({ nanoseconds, orderbook, tradingState, tradingActionReason }, bytes)

@[simp] theorem encode_length (message : OrderbookTradingActionMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradingState.encode_length, TradingActionReason.encode_length]

theorem encode_length_pos (message : OrderbookTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradingState.decode_encode, some_bind]
  dsimp only
  rw [TradingActionReason.decode_encode, some_bind]
  rfl

end OrderbookTradingActionMessage

/-- Orderbook Reference Price Message: 14 bytes -/
structure OrderbookReferencePriceMessage where
  nanoseconds : BitVec 32
  orderbook : BitVec 32
  referencePrice : BitVec 32
  priceType : PriceType
  referencePriceReason : ReferencePriceReason
  deriving DecidableEq, Repr

namespace OrderbookReferencePriceMessage

def encode (message : OrderbookReferencePriceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.referencePrice
    ++ (PriceType.encode message.priceType
    ++ (ReferencePriceReason.encode message.referencePriceReason))))

def decode (bytes : List UInt8) : Option (OrderbookReferencePriceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (referencePrice, bytes) ← decodeUInt 4 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (referencePriceReason, bytes) ← ReferencePriceReason.decode bytes
  pure ({ nanoseconds, orderbook, referencePrice, priceType, referencePriceReason }, bytes)

@[simp] theorem encode_length (message : OrderbookReferencePriceMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, PriceType.encode_length, ReferencePriceReason.encode_length]

theorem encode_length_pos (message : OrderbookReferencePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookReferencePriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [ReferencePriceReason.decode_encode, some_bind]
  rfl

end OrderbookReferencePriceMessage

/-- Add Order Message: 33 bytes -/
structure AddOrderMessage where
  nanoseconds : BitVec 32
  orderNumber : BitVec 64
  orderVerb : OrderVerb
  quantity : BitVec 64
  orderbook : BitVec 32
  price : BitVec 32
  participantId : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderNumber
    ++ (OrderVerb.encode message.orderVerb
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.participantId))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (orderVerb, bytes) ← OrderVerb.decode bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (participantId, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderNumber, orderVerb, quantity, orderbook, price, participantId }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OrderVerb.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderVerb.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessage

/-- Order Executed Message: 34 bytes -/
structure OrderExecutedMessage where
  nanoseconds : BitVec 32
  orderNumber : BitVec 64
  executedQuantity : BitVec 64
  matchNumber : BitVec 64
  tradeIndicator : TradeIndicator
  statUpdate : StatUpdate
  aggressorParticipantId : BitVec 32
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 8 message.matchNumber
    ++ (TradeIndicator.encode message.tradeIndicator
    ++ (StatUpdate.encode message.statUpdate
    ++ (encodeUInt 4 message.aggressorParticipantId))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (tradeIndicator, bytes) ← TradeIndicator.decode bytes
  let (statUpdate, bytes) ← StatUpdate.decode bytes
  let (aggressorParticipantId, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderNumber, executedQuantity, matchNumber, tradeIndicator, statUpdate, aggressorParticipantId }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradeIndicator.encode_length, StatUpdate.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StatUpdate.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Executed With Price Message: 39 bytes -/
structure OrderExecutedWithPriceMessage where
  nanoseconds : BitVec 32
  orderNumber : BitVec 64
  executedQuantity : BitVec 64
  matchNumber : BitVec 64
  tradeIndicator : TradeIndicator
  printable : Printable
  executionPrice : BitVec 32
  statUpdate : StatUpdate
  counterpartyParticipantId : BitVec 32
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 8 message.matchNumber
    ++ (TradeIndicator.encode message.tradeIndicator
    ++ (Printable.encode message.printable
    ++ (encodeUInt 4 message.executionPrice
    ++ (StatUpdate.encode message.statUpdate
    ++ (encodeUInt 4 message.counterpartyParticipantId))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (tradeIndicator, bytes) ← TradeIndicator.decode bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (statUpdate, bytes) ← StatUpdate.decode bytes
  let (counterpartyParticipantId, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderNumber, executedQuantity, matchNumber, tradeIndicator, printable := printable_, executionPrice, statUpdate, counterpartyParticipantId }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradeIndicator.encode_length, Printable.encode_length, StatUpdate.encode_length]

theorem encode_length_pos (message : OrderExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StatUpdate.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedWithPriceMessage

/-- Trade Message: 39 bytes -/
structure TradeMessage where
  nanoseconds : BitVec 32
  executedQuantity : BitVec 64
  orderbook : BitVec 32
  printable : Printable
  executionPrice : BitVec 32
  matchNumber : BitVec 64
  tradeIndicator : TradeIndicator
  statUpdate : StatUpdate
  buyParticipantId : BitVec 32
  sellParticipantId : BitVec 32
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 4 message.orderbook
    ++ (Printable.encode message.printable
    ++ (encodeUInt 4 message.executionPrice
    ++ (encodeUInt 8 message.matchNumber
    ++ (TradeIndicator.encode message.tradeIndicator
    ++ (StatUpdate.encode message.statUpdate
    ++ (encodeUInt 4 message.buyParticipantId
    ++ (encodeUInt 4 message.sellParticipantId)))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (tradeIndicator, bytes) ← TradeIndicator.decode bytes
  let (statUpdate, bytes) ← StatUpdate.decode bytes
  let (buyParticipantId, bytes) ← decodeUInt 4 bytes
  let (sellParticipantId, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, executedQuantity, orderbook, printable := printable_, executionPrice, matchNumber, tradeIndicator, statUpdate, buyParticipantId, sellParticipantId }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length, TradeIndicator.encode_length, StatUpdate.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StatUpdate.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeMessage

/-- Broken Trade Message: 13 bytes -/
structure BrokenTradeMessage where
  nanoseconds : BitVec 32
  matchNumber : BitVec 64
  brokenTradeReason : BrokenTradeReason
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.matchNumber
    ++ (BrokenTradeReason.encode message.brokenTradeReason))

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (brokenTradeReason, bytes) ← BrokenTradeReason.decode bytes
  pure ({ nanoseconds, matchNumber, brokenTradeReason }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BrokenTradeReason.encode_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [BrokenTradeReason.decode_encode, some_bind]
  rfl

end BrokenTradeMessage

/-- Order Delete Message: 12 bytes -/
structure OrderDeleteMessage where
  nanoseconds : BitVec 32
  orderNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderNumber)

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, orderNumber }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDeleteMessage

/-- Order Replace Message: 32 bytes -/
structure OrderReplaceMessage where
  nanoseconds : BitVec 32
  originalOrderNumber : BitVec 64
  newOrderNumber : BitVec 64
  quantity : BitVec 64
  price : BitVec 32
  deriving DecidableEq, Repr

namespace OrderReplaceMessage

def encode (message : OrderReplaceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.originalOrderNumber
    ++ (encodeUInt 8 message.newOrderNumber
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.price))))

def decode (bytes : List UInt8) : Option (OrderReplaceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (originalOrderNumber, bytes) ← decodeUInt 8 bytes
  let (newOrderNumber, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, originalOrderNumber, newOrderNumber, quantity, price }, bytes)

@[simp] theorem encode_length (message : OrderReplaceMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderReplaceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end OrderReplaceMessage

/-- Indicative Price Quantity Message: 29 bytes -/
structure IndicativePriceQuantityMessage where
  nanoseconds : BitVec 32
  theoreticalOpeningQuantity : BitVec 64
  orderbook : BitVec 32
  bestBid : BitVec 32
  bestOffer : BitVec 32
  theoreticalOpeningPrice : BitVec 32
  crossType : CrossType
  deriving DecidableEq, Repr

namespace IndicativePriceQuantityMessage

def encode (message : IndicativePriceQuantityMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.theoreticalOpeningQuantity
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.bestBid
    ++ (encodeUInt 4 message.bestOffer
    ++ (encodeUInt 4 message.theoreticalOpeningPrice
    ++ (CrossType.encode message.crossType))))))

def decode (bytes : List UInt8) : Option (IndicativePriceQuantityMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (theoreticalOpeningQuantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (bestBid, bytes) ← decodeUInt 4 bytes
  let (bestOffer, bytes) ← decodeUInt 4 bytes
  let (theoreticalOpeningPrice, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  pure ({ nanoseconds, theoreticalOpeningQuantity, orderbook, bestBid, bestOffer, theoreticalOpeningPrice, crossType }, bytes)

@[simp] theorem encode_length (message : IndicativePriceQuantityMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CrossType.encode_length]

theorem encode_length_pos (message : IndicativePriceQuantityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicativePriceQuantityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [CrossType.decode_encode, some_bind]
  rfl

end IndicativePriceQuantityMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | timeStampSecondsMessage (message : TimeStampSecondsMessage) -- "T" 0x54
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | priceTickSizeMessage (message : PriceTickSizeMessage) -- "L" 0x4C
  | quantityTickSizeMessage (message : QuantityTickSizeMessage) -- "M" 0x4D
  | orderbookDirectoryMessage (message : OrderbookDirectoryMessage) -- "R" 0x52
  | participantDirectoryMessage (message : ParticipantDirectoryMessage) -- "F" 0x46
  | orderbookTradingActionMessage (message : OrderbookTradingActionMessage) -- "H" 0x48
  | orderbookReferencePriceMessage (message : OrderbookReferencePriceMessage) -- "X" 0x58
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- "C" 0x43
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  | orderDeleteMessage (message : OrderDeleteMessage) -- "D" 0x44
  | orderReplaceMessage (message : OrderReplaceMessage) -- "U" 0x55
  | indicativePriceQuantityMessage (message : IndicativePriceQuantityMessage) -- "I" 0x49
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .timeStampSecondsMessage _ => 84
  | .systemEventMessage _ => 83
  | .priceTickSizeMessage _ => 76
  | .quantityTickSizeMessage _ => 77
  | .orderbookDirectoryMessage _ => 82
  | .participantDirectoryMessage _ => 70
  | .orderbookTradingActionMessage _ => 72
  | .orderbookReferencePriceMessage _ => 88
  | .addOrderMessage _ => 65
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .tradeMessage _ => 80
  | .brokenTradeMessage _ => 66
  | .orderDeleteMessage _ => 68
  | .orderReplaceMessage _ => 85
  | .indicativePriceQuantityMessage _ => 73

def encode : Payload → List UInt8
  | .timeStampSecondsMessage message => TimeStampSecondsMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .priceTickSizeMessage message => PriceTickSizeMessage.encode message
  | .quantityTickSizeMessage message => QuantityTickSizeMessage.encode message
  | .orderbookDirectoryMessage message => OrderbookDirectoryMessage.encode message
  | .participantDirectoryMessage message => ParticipantDirectoryMessage.encode message
  | .orderbookTradingActionMessage message => OrderbookTradingActionMessage.encode message
  | .orderbookReferencePriceMessage message => OrderbookReferencePriceMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderReplaceMessage message => OrderReplaceMessage.encode message
  | .indicativePriceQuantityMessage message => IndicativePriceQuantityMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 99 := by
  cases message with
  | timeStampSecondsMessage inner =>
    simp only [encode, TimeStampSecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | priceTickSizeMessage inner =>
    simp only [encode, PriceTickSizeMessage.encode_length]
    omega
  | quantityTickSizeMessage inner =>
    simp only [encode, QuantityTickSizeMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [encode, OrderbookDirectoryMessage.encode_length]
    omega
  | participantDirectoryMessage inner =>
    simp only [encode, ParticipantDirectoryMessage.encode_length]
    omega
  | orderbookTradingActionMessage inner =>
    simp only [encode, OrderbookTradingActionMessage.encode_length]
    omega
  | orderbookReferencePriceMessage inner =>
    simp only [encode, OrderbookReferencePriceMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [encode, OrderExecutedWithPriceMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [encode, OrderDeleteMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [encode, OrderReplaceMessage.encode_length]
    omega
  | indicativePriceQuantityMessage inner =>
    simp only [encode, IndicativePriceQuantityMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (TimeStampSecondsMessage.decode bytes).map fun (message, rest) => (.timeStampSecondsMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 76 then (PriceTickSizeMessage.decode bytes).map fun (message, rest) => (.priceTickSizeMessage message, rest)
  else if tag = 77 then (QuantityTickSizeMessage.decode bytes).map fun (message, rest) => (.quantityTickSizeMessage message, rest)
  else if tag = 82 then (OrderbookDirectoryMessage.decode bytes).map fun (message, rest) => (.orderbookDirectoryMessage message, rest)
  else if tag = 70 then (ParticipantDirectoryMessage.decode bytes).map fun (message, rest) => (.participantDirectoryMessage message, rest)
  else if tag = 72 then (OrderbookTradingActionMessage.decode bytes).map fun (message, rest) => (.orderbookTradingActionMessage message, rest)
  else if tag = 88 then (OrderbookReferencePriceMessage.decode bytes).map fun (message, rest) => (.orderbookReferencePriceMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 85 then (OrderReplaceMessage.decode bytes).map fun (message, rest) => (.orderReplaceMessage message, rest)
  else if tag = 73 then (IndicativePriceQuantityMessage.decode bytes).map fun (message, rest) => (.indicativePriceQuantityMessage message, rest)
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
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | timeStampSecondsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TimeStampSecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | priceTickSizeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PriceTickSizeMessage.encode_length]
    omega
  | quantityTickSizeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuantityTickSizeMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderbookDirectoryMessage.encode_length]
    omega
  | participantDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ParticipantDirectoryMessage.encode_length]
    omega
  | orderbookTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderbookTradingActionMessage.encode_length]
    omega
  | orderbookReferencePriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderbookReferencePriceMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderReplaceMessage.encode_length]
    omega
  | indicativePriceQuantityMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndicativePriceQuantityMessage.encode_length]
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

end Omi.BivaBivaequitiesTotalviewItchV112
