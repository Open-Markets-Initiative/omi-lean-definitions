import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Depth Of Market v2.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNtxoptionsDepthofmarketItchV22Server

/-- Reject Reason Code: one byte code -/
def RejectReasonCode.codes : List UInt8 :=
  [0x41, 0x53]

inductive RejectReasonCode where
  | notAuthorized -- Not Authorized
  | sessionNotAvailable -- Session Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectReasonCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectReasonCode

def toByte : RejectReasonCode → UInt8
  | .notAuthorized => 0x41
  | .sessionNotAvailable => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectReasonCode :=
  if byte = 0x41 then .notAuthorized
  else .sessionNotAvailable

def ofByte (byte : UInt8) : RejectReasonCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectReasonCode) : ofByte value.toByte = value := by
  cases value with
  | notAuthorized => decide
  | sessionNotAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RejectReasonCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RejectReasonCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RejectReasonCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RejectReasonCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RejectReasonCode

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4E, 0x4C, 0x45, 0x43]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfOpeningProcess -- Start Of Opening Process
  | endOfNormalHoursProcessing -- End Of Normal Hours Processing
  | endOfLateHoursProcessing -- End Of Late Hours Processing
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfOpeningProcess => 0x51
  | .endOfNormalHoursProcessing => 0x4E
  | .endOfLateHoursProcessing => 0x4C
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfOpeningProcess
  else if byte = 0x4E then .endOfNormalHoursProcessing
  else if byte = 0x4C then .endOfLateHoursProcessing
  else if byte = 0x45 then .endOfSystemHours
  else .endOfMessages

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfOpeningProcess => decide
  | endOfNormalHoursProcessing => decide
  | endOfLateHoursProcessing => decide
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

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x43, 0x50, 0x4E]

inductive OptionType where
  | callOption -- Call Option
  | putOption -- Put Option
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .callOption => 0x43
  | .putOption => 0x50
  | .na => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .callOption
  else if byte = 0x50 then .putOption
  else .na

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | callOption => decide
  | putOption => decide
  | na => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionType

/-- Closing Type: one byte code -/
def ClosingType.codes : List UInt8 :=
  [0x4E, 0x4C]

inductive ClosingType where
  | normalHours -- Normal Hours
  | lateHours -- Late Hours
  | unlisted (byte : { byte : UInt8 // byte ∉ ClosingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClosingType

def toByte : ClosingType → UInt8
  | .normalHours => 0x4E
  | .lateHours => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClosingType :=
  if byte = 0x4E then .normalHours
  else .lateHours

def ofByte (byte : UInt8) : ClosingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClosingType) : ofByte value.toByte = value := by
  cases value with
  | normalHours => decide
  | lateHours => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClosingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClosingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClosingType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ClosingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClosingType

/-- Tradable: one byte code -/
def Tradable.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Tradable where
  | instrumentIsTradable -- Instrument Is Tradable
  | instrumentIsNotTradable -- Instrument Is Not Tradable
  | unlisted (byte : { byte : UInt8 // byte ∉ Tradable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tradable

def toByte : Tradable → UInt8
  | .instrumentIsTradable => 0x59
  | .instrumentIsNotTradable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tradable :=
  if byte = 0x59 then .instrumentIsTradable
  else .instrumentIsNotTradable

def ofByte (byte : UInt8) : Tradable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tradable) : ofByte value.toByte = value := by
  cases value with
  | instrumentIsTradable => decide
  | instrumentIsNotTradable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Tradable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Tradable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Tradable) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Tradable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Tradable

/-- Mpv: one byte code -/
def Mpv.codes : List UInt8 :=
  [0x45, 0x53, 0x50]

inductive Mpv where
  | pennyEverywhere -- Penny Everywhere
  | scaled -- Scaled
  | pennyPilot -- Penny Pilot
  | unlisted (byte : { byte : UInt8 // byte ∉ Mpv.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Mpv

def toByte : Mpv → UInt8
  | .pennyEverywhere => 0x45
  | .scaled => 0x53
  | .pennyPilot => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Mpv :=
  if byte = 0x45 then .pennyEverywhere
  else if byte = 0x53 then .scaled
  else .pennyPilot

def ofByte (byte : UInt8) : Mpv :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Mpv) : ofByte value.toByte = value := by
  cases value with
  | pennyEverywhere => decide
  | scaled => decide
  | pennyPilot => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Mpv) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Mpv × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Mpv) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Mpv) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Mpv

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x48, 0x42, 0x53, 0x49, 0x4F, 0x52, 0x54, 0x58]

inductive CurrentTradingState where
  | haltInEffect -- Halt In Effect
  | buySideTradingSuspended -- Buy Side Trading Suspended
  | sellSideTradingSuspended -- Sell Side Trading Suspended
  | preOpen -- Pre Open
  | openingAuction -- Opening Auction
  | reOpening -- Re Opening
  | continuousTrading -- Continuous Trading
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .haltInEffect => 0x48
  | .buySideTradingSuspended => 0x42
  | .sellSideTradingSuspended => 0x53
  | .preOpen => 0x49
  | .openingAuction => 0x4F
  | .reOpening => 0x52
  | .continuousTrading => 0x54
  | .closed => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .haltInEffect
  else if byte = 0x42 then .buySideTradingSuspended
  else if byte = 0x53 then .sellSideTradingSuspended
  else if byte = 0x49 then .preOpen
  else if byte = 0x4F then .openingAuction
  else if byte = 0x52 then .reOpening
  else if byte = 0x54 then .continuousTrading
  else .closed

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | haltInEffect => decide
  | buySideTradingSuspended => decide
  | sellSideTradingSuspended => decide
  | preOpen => decide
  | openingAuction => decide
  | reOpening => decide
  | continuousTrading => decide
  | closed => decide
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

/-- Market Side: one byte code -/
def MarketSide.codes : List UInt8 :=
  [0x42, 0x53, 0x58, 0x59]

inductive MarketSide where
  | buy -- Buy
  | sell -- Sell
  | buyAon -- Buy Aon
  | sellAon -- Sell Aon
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketSide

def toByte : MarketSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .buyAon => 0x58
  | .sellAon => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x58 then .buyAon
  else .sellAon

def ofByte (byte : UInt8) : MarketSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | buyAon => decide
  | sellAon => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketSide

/-- Printable: one byte code -/
def Printable.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Printable where
  | nonprintable -- Nonprintable
  | printable -- Printable
  | unlisted (byte : { byte : UInt8 // byte ∉ Printable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Printable

def toByte : Printable → UInt8
  | .nonprintable => 0x4E
  | .printable => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Printable :=
  if byte = 0x4E then .nonprintable
  else .printable

def ofByte (byte : UInt8) : Printable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Printable) : ofByte value.toByte = value := by
  cases value with
  | nonprintable => decide
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

/-- Change Reason: one byte code -/
def ChangeReason.codes : List UInt8 :=
  [0x55, 0x52, 0x53]

inductive ChangeReason where
  | user -- User
  | reprice -- Reprice
  | suspend -- Suspend
  | unlisted (byte : { byte : UInt8 // byte ∉ ChangeReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ChangeReason

def toByte : ChangeReason → UInt8
  | .user => 0x55
  | .reprice => 0x52
  | .suspend => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ChangeReason :=
  if byte = 0x55 then .user
  else if byte = 0x52 then .reprice
  else .suspend

def ofByte (byte : UInt8) : ChangeReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ChangeReason) : ofByte value.toByte = value := by
  cases value with
  | user => decide
  | reprice => decide
  | suspend => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ChangeReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ChangeReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ChangeReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ChangeReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ChangeReason

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x41, 0x50, 0x4E]

inductive CrossType where
  | allAuctions -- All Auctions
  | priceImprovement -- Price Improvement
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .allAuctions => 0x41
  | .priceImprovement => 0x50
  | .none_ => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x41 then .allAuctions
  else if byte = 0x50 then .priceImprovement
  else .none_

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | allAuctions => decide
  | priceImprovement => decide
  | none_ => decide
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

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x45]

inductive TradeType where
  | electronicTrade -- Electronic Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .electronicTrade => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : TradeType :=
  .electronicTrade

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | electronicTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeType

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x4F, 0x52, 0x50, 0x49]

inductive AuctionType where
  | opening -- Opening
  | reopening -- Reopening
  | priceImprovement -- Price Improvement
  | orderExposure -- Order Exposure
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .opening => 0x4F
  | .reopening => 0x52
  | .priceImprovement => 0x50
  | .orderExposure => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x4F then .opening
  else if byte = 0x52 then .reopening
  else if byte = 0x50 then .priceImprovement
  else .orderExposure

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | opening => decide
  | reopening => decide
  | priceImprovement => decide
  | orderExposure => decide
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

/-- Imbalance Direction: one byte code -/
def ImbalanceDirection.codes : List UInt8 :=
  [0x42, 0x53]

inductive ImbalanceDirection where
  | buyImbalance -- Buy Imbalance
  | sellImbalance -- Sell Imbalance
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceDirection

def toByte : ImbalanceDirection → UInt8
  | .buyImbalance => 0x42
  | .sellImbalance => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceDirection :=
  if byte = 0x42 then .buyImbalance
  else .sellImbalance

def ofByte (byte : UInt8) : ImbalanceDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceDirection) : ofByte value.toByte = value := by
  cases value with
  | buyImbalance => decide
  | sellImbalance => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ImbalanceDirection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceDirection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceDirection) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ImbalanceDirection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ImbalanceDirection

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  debugText : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.debugText

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (debugText, bytes) ← Alpha.decode 1 bytes
  pure ({ debugText }, bytes)

@[simp] theorem encode_length (message : DebugPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DebugPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebugPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DebugPacket

/-- Login Accepted Packet: 30 bytes -/
structure LoginAcceptedPacket where
  acceptedSession : Alpha 10
  acceptedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.acceptedSession
    ++ (Alpha.encode message.acceptedSequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (acceptedSession, bytes) ← Alpha.decode 10 bytes
  let (acceptedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ acceptedSession, acceptedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : RejectReasonCode
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  RejectReasonCode.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← RejectReasonCode.decode bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [RejectReasonCode.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RejectReasonCode.decode_encode, some_bind]
  rfl

end LoginRejectedPacket

/-- System Event Message: 11 bytes -/
structure SystemEventMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (EventCode.encode message.eventCode))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ trackingNumber, timestamp, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Derivative Directory Message: 86 bytes -/
structure DerivativeDirectoryMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  securitySymbol : Alpha 6
  expirationYear : BitVec 8
  expirationMonth : BitVec 8
  expirationDate : BitVec 8
  explicitStrikePrice : BitVec 32
  optionType : OptionType
  underlyingSymbol : Alpha 13
  closingType : ClosingType
  tradable : Tradable
  mpv : Mpv
  isin : Alpha 12
  tickSizeTableId : BitVec 16
  priceNotation : Alpha 1
  volumeNotation : Alpha 1
  financialProduct : BitVec 16
  marketSegmentId : Alpha 1
  tradingCurrency : Alpha 3
  mic : Alpha 4
  instrumentLongName : Alpha 16
  deriving DecidableEq, Repr

namespace DerivativeDirectoryMessage

def encode (message : DerivativeDirectoryMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 1 message.expirationYear
    ++ (encodeUInt 1 message.expirationMonth
    ++ (encodeUInt 1 message.expirationDate
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.underlyingSymbol
    ++ (ClosingType.encode message.closingType
    ++ (Tradable.encode message.tradable
    ++ (Mpv.encode message.mpv
    ++ (Alpha.encode message.isin
    ++ (encodeUInt 2 message.tickSizeTableId
    ++ (Alpha.encode message.priceNotation
    ++ (Alpha.encode message.volumeNotation
    ++ (encodeUInt 2 message.financialProduct
    ++ (Alpha.encode message.marketSegmentId
    ++ (Alpha.encode message.tradingCurrency
    ++ (Alpha.encode message.mic
    ++ (Alpha.encode message.instrumentLongName)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (DerivativeDirectoryMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 6 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  let (expirationMonth, bytes) ← decodeUInt 1 bytes
  let (expirationDate, bytes) ← decodeUInt 1 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (closingType, bytes) ← ClosingType.decode bytes
  let (tradable, bytes) ← Tradable.decode bytes
  let (mpv, bytes) ← Mpv.decode bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (tickSizeTableId, bytes) ← decodeUInt 2 bytes
  let (priceNotation, bytes) ← Alpha.decode 1 bytes
  let (volumeNotation, bytes) ← Alpha.decode 1 bytes
  let (financialProduct, bytes) ← decodeUInt 2 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 1 bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (instrumentLongName, bytes) ← Alpha.decode 16 bytes
  pure ({ trackingNumber, timestamp, instrumentId, securitySymbol, expirationYear, expirationMonth, expirationDate, explicitStrikePrice, optionType, underlyingSymbol, closingType, tradable, mpv, isin, tickSizeTableId, priceNotation, volumeNotation, financialProduct, marketSegmentId, tradingCurrency, mic, instrumentLongName }, bytes)

@[simp] theorem encode_length (message : DerivativeDirectoryMessage) : (encode message).length = 86 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, ClosingType.encode_length, Tradable.encode_length, Mpv.encode_length]

theorem encode_length_pos (message : DerivativeDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DerivativeDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClosingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tradable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Mpv.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DerivativeDirectoryMessage

/-- Trading Action Message: 15 bytes -/
structure TradingActionMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace TradingActionMessage

def encode (message : TradingActionMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (CurrentTradingState.encode message.currentTradingState)))

def decode (bytes : List UInt8) : Option (TradingActionMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ trackingNumber, timestamp, instrumentId, currentTradingState }, bytes)

@[simp] theorem encode_length (message : TradingActionMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : TradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CurrentTradingState.decode_encode, some_bind]
  rfl

end TradingActionMessage

/-- Add Order Short Form Message: 30 bytes -/
structure AddOrderShortFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderReferenceNumber : BitVec 64
  marketSide : MarketSide
  orderCapacity : Alpha 1
  priceShort : BitVec 16
  volumeShort : BitVec 16
  rank : BitVec 16
  deriving DecidableEq, Repr

namespace AddOrderShortFormMessage

def encode (message : AddOrderShortFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (MarketSide.encode message.marketSide
    ++ (Alpha.encode message.orderCapacity
    ++ (encodeUInt 2 message.priceShort
    ++ (encodeUInt 2 message.volumeShort
    ++ (encodeUInt 2 message.rank))))))))

def decode (bytes : List UInt8) : Option (AddOrderShortFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (marketSide, bytes) ← MarketSide.decode bytes
  let (orderCapacity, bytes) ← Alpha.decode 1 bytes
  let (priceShort, bytes) ← decodeUInt 2 bytes
  let (volumeShort, bytes) ← decodeUInt 2 bytes
  let (rank, bytes) ← decodeUInt 2 bytes
  pure ({ trackingNumber, timestamp, instrumentId, orderReferenceNumber, marketSide, orderCapacity, priceShort, volumeShort, rank }, bytes)

@[simp] theorem encode_length (message : AddOrderShortFormMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, MarketSide.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderShortFormMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, MarketSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderShortFormMessage

/-- Add Order Long Form Message: 34 bytes -/
structure AddOrderLongFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderReferenceNumber : BitVec 64
  marketSide : MarketSide
  orderCapacity : Alpha 1
  priceLong : BitVec 32
  volumeLong : BitVec 32
  rank : BitVec 16
  deriving DecidableEq, Repr

namespace AddOrderLongFormMessage

def encode (message : AddOrderLongFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (MarketSide.encode message.marketSide
    ++ (Alpha.encode message.orderCapacity
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong
    ++ (encodeUInt 2 message.rank))))))))

def decode (bytes : List UInt8) : Option (AddOrderLongFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (marketSide, bytes) ← MarketSide.decode bytes
  let (orderCapacity, bytes) ← Alpha.decode 1 bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  let (rank, bytes) ← decodeUInt 2 bytes
  pure ({ trackingNumber, timestamp, instrumentId, orderReferenceNumber, marketSide, orderCapacity, priceLong, volumeLong, rank }, bytes)

@[simp] theorem encode_length (message : AddOrderLongFormMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, MarketSide.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderLongFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderLongFormMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, MarketSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderLongFormMessage

/-- Add Quote Short Form Message: 38 bytes -/
structure AddQuoteShortFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  bidReferenceNumber : BitVec 64
  askReferenceNumber : BitVec 64
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  askPriceShort : BitVec 16
  askSizeShort : BitVec 16
  deriving DecidableEq, Repr

namespace AddQuoteShortFormMessage

def encode (message : AddQuoteShortFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.bidReferenceNumber
    ++ (encodeUInt 8 message.askReferenceNumber
    ++ (encodeUInt 2 message.bidPriceShort
    ++ (encodeUInt 2 message.bidSizeShort
    ++ (encodeUInt 2 message.askPriceShort
    ++ (encodeUInt 2 message.askSizeShort))))))))

def decode (bytes : List UInt8) : Option (AddQuoteShortFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (askReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (bidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bidSizeShort, bytes) ← decodeUInt 2 bytes
  let (askPriceShort, bytes) ← decodeUInt 2 bytes
  let (askSizeShort, bytes) ← decodeUInt 2 bytes
  pure ({ trackingNumber, timestamp, instrumentId, bidReferenceNumber, askReferenceNumber, bidPriceShort, bidSizeShort, askPriceShort, askSizeShort }, bytes)

@[simp] theorem encode_length (message : AddQuoteShortFormMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AddQuoteShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddQuoteShortFormMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddQuoteShortFormMessage

/-- Add Quote Long Form Message: 46 bytes -/
structure AddQuoteLongFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  bidReferenceNumber : BitVec 64
  askReferenceNumber : BitVec 64
  bidPriceLong : BitVec 32
  bidSizeLong : BitVec 32
  askPriceLong : BitVec 32
  askSizeLong : BitVec 32
  deriving DecidableEq, Repr

namespace AddQuoteLongFormMessage

def encode (message : AddQuoteLongFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.bidReferenceNumber
    ++ (encodeUInt 8 message.askReferenceNumber
    ++ (encodeUInt 4 message.bidPriceLong
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 4 message.askPriceLong
    ++ (encodeUInt 4 message.askSizeLong))))))))

def decode (bytes : List UInt8) : Option (AddQuoteLongFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (askReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (bidPriceLong, bytes) ← decodeUInt 4 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (askPriceLong, bytes) ← decodeUInt 4 bytes
  let (askSizeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, bidReferenceNumber, askReferenceNumber, bidPriceLong, bidSizeLong, askPriceLong, askSizeLong }, bytes)

@[simp] theorem encode_length (message : AddQuoteLongFormMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AddQuoteLongFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddQuoteLongFormMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddQuoteLongFormMessage

/-- Order Executed Message: 38 bytes -/
structure OrderExecutedMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  strategyId : BitVec 32
  referenceNumber : BitVec 64
  executedVolume : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 8 message.referenceNumber
    ++ (encodeUInt 4 message.executedVolume
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber)))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (referenceNumber, bytes) ← decodeUInt 8 bytes
  let (executedVolume, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, strategyId, referenceNumber, executedVolume, crossNumber, matchNumber }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Executed With Price Message: 43 bytes -/
structure OrderExecutedWithPriceMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  strategyId : BitVec 32
  referenceNumber : BitVec 64
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  printable : Printable
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 8 message.referenceNumber
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber
    ++ (Printable.encode message.printable
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong)))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (referenceNumber, bytes) ← decodeUInt 8 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, strategyId, referenceNumber, crossNumber, matchNumber, printable := printable_, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length]

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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedWithPriceMessage

/-- Order Cancel Message: 26 bytes -/
structure OrderCancelMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderReferenceNumber : BitVec 64
  cancelledVolume : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeUInt 4 message.cancelledVolume))))

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (cancelledVolume, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, orderReferenceNumber, cancelledVolume }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelMessage) (rest : List UInt8) :
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

end OrderCancelMessage

/-- Order Replace Short Form Message: 34 bytes -/
structure OrderReplaceShortFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  originalReferenceNumber : BitVec 64
  newReferenceNumber : BitVec 64
  priceShort : BitVec 16
  volumeShort : BitVec 16
  deriving DecidableEq, Repr

namespace OrderReplaceShortFormMessage

def encode (message : OrderReplaceShortFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.originalReferenceNumber
    ++ (encodeUInt 8 message.newReferenceNumber
    ++ (encodeUInt 2 message.priceShort
    ++ (encodeUInt 2 message.volumeShort))))))

def decode (bytes : List UInt8) : Option (OrderReplaceShortFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (originalReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (newReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (priceShort, bytes) ← decodeUInt 2 bytes
  let (volumeShort, bytes) ← decodeUInt 2 bytes
  pure ({ trackingNumber, timestamp, instrumentId, originalReferenceNumber, newReferenceNumber, priceShort, volumeShort }, bytes)

@[simp] theorem encode_length (message : OrderReplaceShortFormMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderReplaceShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceShortFormMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderReplaceShortFormMessage

/-- Order Replace Long Form Message: 38 bytes -/
structure OrderReplaceLongFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  originalReferenceNumber : BitVec 64
  newReferenceNumber : BitVec 64
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace OrderReplaceLongFormMessage

def encode (message : OrderReplaceLongFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.originalReferenceNumber
    ++ (encodeUInt 8 message.newReferenceNumber
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong))))))

def decode (bytes : List UInt8) : Option (OrderReplaceLongFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (originalReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (newReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, originalReferenceNumber, newReferenceNumber, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : OrderReplaceLongFormMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderReplaceLongFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceLongFormMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderReplaceLongFormMessage

/-- Order Delete Message: 22 bytes -/
structure OrderDeleteMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  referenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.referenceNumber)))

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (referenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ trackingNumber, timestamp, instrumentId, referenceNumber }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 22 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDeleteMessage

/-- Order Change Message: 31 bytes -/
structure OrderChangeMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  referenceNumber : BitVec 64
  changeReason : ChangeReason
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace OrderChangeMessage

def encode (message : OrderChangeMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.referenceNumber
    ++ (ChangeReason.encode message.changeReason
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong))))))

def decode (bytes : List UInt8) : Option (OrderChangeMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (referenceNumber, bytes) ← decodeUInt 8 bytes
  let (changeReason, bytes) ← ChangeReason.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, referenceNumber, changeReason, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : OrderChangeMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ChangeReason.encode_length]

theorem encode_length_pos (message : OrderChangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderChangeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ChangeReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderChangeMessage

/-- Quote Replace Short Form Message: 54 bytes -/
structure QuoteReplaceShortFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  originalBidReferenceNumber : BitVec 64
  bidReferenceNumber : BitVec 64
  originalAskReferenceNumber : BitVec 64
  askReferenceNumber : BitVec 64
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  askPriceShort : BitVec 16
  askSizeShort : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteReplaceShortFormMessage

def encode (message : QuoteReplaceShortFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.originalBidReferenceNumber
    ++ (encodeUInt 8 message.bidReferenceNumber
    ++ (encodeUInt 8 message.originalAskReferenceNumber
    ++ (encodeUInt 8 message.askReferenceNumber
    ++ (encodeUInt 2 message.bidPriceShort
    ++ (encodeUInt 2 message.bidSizeShort
    ++ (encodeUInt 2 message.askPriceShort
    ++ (encodeUInt 2 message.askSizeShort))))))))))

def decode (bytes : List UInt8) : Option (QuoteReplaceShortFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (originalBidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (bidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (originalAskReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (askReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (bidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bidSizeShort, bytes) ← decodeUInt 2 bytes
  let (askPriceShort, bytes) ← decodeUInt 2 bytes
  let (askSizeShort, bytes) ← decodeUInt 2 bytes
  pure ({ trackingNumber, timestamp, instrumentId, originalBidReferenceNumber, bidReferenceNumber, originalAskReferenceNumber, askReferenceNumber, bidPriceShort, bidSizeShort, askPriceShort, askSizeShort }, bytes)

@[simp] theorem encode_length (message : QuoteReplaceShortFormMessage) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : QuoteReplaceShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteReplaceShortFormMessage) (rest : List UInt8) :
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

end QuoteReplaceShortFormMessage

/-- Quote Replace Long Form Message: 62 bytes -/
structure QuoteReplaceLongFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  originalBidReferenceNumber : BitVec 64
  bidReferenceNumber : BitVec 64
  originalAskReferenceNumber : BitVec 64
  askReferenceNumber : BitVec 64
  bidPriceLong : BitVec 32
  bidSizeLong : BitVec 32
  askPriceLong : BitVec 32
  askSizeLong : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteReplaceLongFormMessage

def encode (message : QuoteReplaceLongFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.originalBidReferenceNumber
    ++ (encodeUInt 8 message.bidReferenceNumber
    ++ (encodeUInt 8 message.originalAskReferenceNumber
    ++ (encodeUInt 8 message.askReferenceNumber
    ++ (encodeUInt 4 message.bidPriceLong
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 4 message.askPriceLong
    ++ (encodeUInt 4 message.askSizeLong))))))))))

def decode (bytes : List UInt8) : Option (QuoteReplaceLongFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (originalBidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (bidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (originalAskReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (askReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (bidPriceLong, bytes) ← decodeUInt 4 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (askPriceLong, bytes) ← decodeUInt 4 bytes
  let (askSizeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, originalBidReferenceNumber, bidReferenceNumber, originalAskReferenceNumber, askReferenceNumber, bidPriceLong, bidSizeLong, askPriceLong, askSizeLong }, bytes)

@[simp] theorem encode_length (message : QuoteReplaceLongFormMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : QuoteReplaceLongFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteReplaceLongFormMessage) (rest : List UInt8) :
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

end QuoteReplaceLongFormMessage

/-- Quote Delete Message: 30 bytes -/
structure QuoteDeleteMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  bidReferenceNumber : BitVec 64
  askReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteDeleteMessage

def encode (message : QuoteDeleteMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.bidReferenceNumber
    ++ (encodeUInt 8 message.askReferenceNumber))))

def decode (bytes : List UInt8) : Option (QuoteDeleteMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (askReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ trackingNumber, timestamp, instrumentId, bidReferenceNumber, askReferenceNumber }, bytes)

@[simp] theorem encode_length (message : QuoteDeleteMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : QuoteDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteDeleteMessage) (rest : List UInt8) :
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

end QuoteDeleteMessage

/-- Trade Message: 37 bytes -/
structure TradeMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  strategyId : BitVec 32
  crossType : CrossType
  priceLong : BitVec 32
  volumeLong : BitVec 32
  printable : Printable
  tradeType : TradeType
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 4 message.strategyId
    ++ (CrossType.encode message.crossType
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong
    ++ (Printable.encode message.printable
    ++ (TradeType.encode message.tradeType))))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  pure ({ trackingNumber, timestamp, instrumentId, crossNumber, matchNumber, strategyId, crossType, priceLong, volumeLong, printable := printable_, tradeType }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CrossType.encode_length, Printable.encode_length, TradeType.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [TradeType.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Net Order Imbalance Message: 49 bytes -/
structure NetOrderImbalanceMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  auctionId : BitVec 32
  auctionType : AuctionType
  pairedQuantity : BitVec 32
  imbalanceDirection : ImbalanceDirection
  imbalancePrice : BitVec 32
  imbalanceVolume : BitVec 32
  customerFirmIndicator : Alpha 1
  bestBidPrice : BitVec 32
  bestBidQuantity : BitVec 32
  bestAskPrice : BitVec 32
  bestAskQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace NetOrderImbalanceMessage

def encode (message : NetOrderImbalanceMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.auctionId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.pairedQuantity
    ++ (ImbalanceDirection.encode message.imbalanceDirection
    ++ (encodeUInt 4 message.imbalancePrice
    ++ (encodeUInt 4 message.imbalanceVolume
    ++ (Alpha.encode message.customerFirmIndicator
    ++ (encodeUInt 4 message.bestBidPrice
    ++ (encodeUInt 4 message.bestBidQuantity
    ++ (encodeUInt 4 message.bestAskPrice
    ++ (encodeUInt 4 message.bestAskQuantity)))))))))))))

def decode (bytes : List UInt8) : Option (NetOrderImbalanceMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (pairedQuantity, bytes) ← decodeUInt 4 bytes
  let (imbalanceDirection, bytes) ← ImbalanceDirection.decode bytes
  let (imbalancePrice, bytes) ← decodeUInt 4 bytes
  let (imbalanceVolume, bytes) ← decodeUInt 4 bytes
  let (customerFirmIndicator, bytes) ← Alpha.decode 1 bytes
  let (bestBidPrice, bytes) ← decodeUInt 4 bytes
  let (bestBidQuantity, bytes) ← decodeUInt 4 bytes
  let (bestAskPrice, bytes) ← decodeUInt 4 bytes
  let (bestAskQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, auctionId, auctionType, pairedQuantity, imbalanceDirection, imbalancePrice, imbalanceVolume, customerFirmIndicator, bestBidPrice, bestBidQuantity, bestAskPrice, bestAskQuantity }, bytes)

@[simp] theorem encode_length (message : NetOrderImbalanceMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, AuctionType.encode_length, ImbalanceDirection.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : NetOrderImbalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetOrderImbalanceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ImbalanceDirection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetOrderImbalanceMessage

/-- End Of Replay Sequence Message: 20 bytes -/
structure EndOfReplaySequenceMessage where
  endOfReplaySequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace EndOfReplaySequenceMessage

def encode (message : EndOfReplaySequenceMessage) : List UInt8 :=
  Alpha.encode message.endOfReplaySequenceNumber

def decode (bytes : List UInt8) : Option (EndOfReplaySequenceMessage × List UInt8) := do
  let (endOfReplaySequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ endOfReplaySequenceNumber }, bytes)

@[simp] theorem encode_length (message : EndOfReplaySequenceMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : EndOfReplaySequenceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfReplaySequenceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfReplaySequenceMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | derivativeDirectoryMessage (message : DerivativeDirectoryMessage) -- "R" 0x52
  | tradingActionMessage (message : TradingActionMessage) -- "H" 0x48
  | addOrderShortFormMessage (message : AddOrderShortFormMessage) -- "a" 0x61
  | addOrderLongFormMessage (message : AddOrderLongFormMessage) -- "A" 0x41
  | addQuoteShortFormMessage (message : AddQuoteShortFormMessage) -- "j" 0x6A
  | addQuoteLongFormMessage (message : AddQuoteLongFormMessage) -- "J" 0x4A
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- "C" 0x43
  | orderCancelMessage (message : OrderCancelMessage) -- "X" 0x58
  | orderReplaceShortFormMessage (message : OrderReplaceShortFormMessage) -- "u" 0x75
  | orderReplaceLongFormMessage (message : OrderReplaceLongFormMessage) -- "U" 0x55
  | orderDeleteMessage (message : OrderDeleteMessage) -- "D" 0x44
  | orderChangeMessage (message : OrderChangeMessage) -- "G" 0x47
  | quoteReplaceShortFormMessage (message : QuoteReplaceShortFormMessage) -- "k" 0x6B
  | quoteReplaceLongFormMessage (message : QuoteReplaceLongFormMessage) -- "K" 0x4B
  | quoteDeleteMessage (message : QuoteDeleteMessage) -- "Y" 0x59
  | tradeMessage (message : TradeMessage) -- "Q" 0x51
  | netOrderImbalanceMessage (message : NetOrderImbalanceMessage) -- "I" 0x49
  | endOfReplaySequenceMessage (message : EndOfReplaySequenceMessage) -- "M" 0x4D
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .derivativeDirectoryMessage _ => 82
  | .tradingActionMessage _ => 72
  | .addOrderShortFormMessage _ => 97
  | .addOrderLongFormMessage _ => 65
  | .addQuoteShortFormMessage _ => 106
  | .addQuoteLongFormMessage _ => 74
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .orderCancelMessage _ => 88
  | .orderReplaceShortFormMessage _ => 117
  | .orderReplaceLongFormMessage _ => 85
  | .orderDeleteMessage _ => 68
  | .orderChangeMessage _ => 71
  | .quoteReplaceShortFormMessage _ => 107
  | .quoteReplaceLongFormMessage _ => 75
  | .quoteDeleteMessage _ => 89
  | .tradeMessage _ => 81
  | .netOrderImbalanceMessage _ => 73
  | .endOfReplaySequenceMessage _ => 77

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .derivativeDirectoryMessage message => DerivativeDirectoryMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .addOrderShortFormMessage message => AddOrderShortFormMessage.encode message
  | .addOrderLongFormMessage message => AddOrderLongFormMessage.encode message
  | .addQuoteShortFormMessage message => AddQuoteShortFormMessage.encode message
  | .addQuoteLongFormMessage message => AddQuoteLongFormMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .orderReplaceShortFormMessage message => OrderReplaceShortFormMessage.encode message
  | .orderReplaceLongFormMessage message => OrderReplaceLongFormMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderChangeMessage message => OrderChangeMessage.encode message
  | .quoteReplaceShortFormMessage message => QuoteReplaceShortFormMessage.encode message
  | .quoteReplaceLongFormMessage message => QuoteReplaceLongFormMessage.encode message
  | .quoteDeleteMessage message => QuoteDeleteMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .netOrderImbalanceMessage message => NetOrderImbalanceMessage.encode message
  | .endOfReplaySequenceMessage message => EndOfReplaySequenceMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 86 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | derivativeDirectoryMessage inner =>
    simp only [encode, DerivativeDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [encode, TradingActionMessage.encode_length]
    omega
  | addOrderShortFormMessage inner =>
    simp only [encode, AddOrderShortFormMessage.encode_length]
    omega
  | addOrderLongFormMessage inner =>
    simp only [encode, AddOrderLongFormMessage.encode_length]
    omega
  | addQuoteShortFormMessage inner =>
    simp only [encode, AddQuoteShortFormMessage.encode_length]
    omega
  | addQuoteLongFormMessage inner =>
    simp only [encode, AddQuoteLongFormMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [encode, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [encode, OrderCancelMessage.encode_length]
    omega
  | orderReplaceShortFormMessage inner =>
    simp only [encode, OrderReplaceShortFormMessage.encode_length]
    omega
  | orderReplaceLongFormMessage inner =>
    simp only [encode, OrderReplaceLongFormMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [encode, OrderDeleteMessage.encode_length]
    omega
  | orderChangeMessage inner =>
    simp only [encode, OrderChangeMessage.encode_length]
    omega
  | quoteReplaceShortFormMessage inner =>
    simp only [encode, QuoteReplaceShortFormMessage.encode_length]
    omega
  | quoteReplaceLongFormMessage inner =>
    simp only [encode, QuoteReplaceLongFormMessage.encode_length]
    omega
  | quoteDeleteMessage inner =>
    simp only [encode, QuoteDeleteMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | netOrderImbalanceMessage inner =>
    simp only [encode, NetOrderImbalanceMessage.encode_length]
    omega
  | endOfReplaySequenceMessage inner =>
    simp only [encode, EndOfReplaySequenceMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (DerivativeDirectoryMessage.decode bytes).map fun (message, rest) => (.derivativeDirectoryMessage message, rest)
  else if tag = 72 then (TradingActionMessage.decode bytes).map fun (message, rest) => (.tradingActionMessage message, rest)
  else if tag = 97 then (AddOrderShortFormMessage.decode bytes).map fun (message, rest) => (.addOrderShortFormMessage message, rest)
  else if tag = 65 then (AddOrderLongFormMessage.decode bytes).map fun (message, rest) => (.addOrderLongFormMessage message, rest)
  else if tag = 106 then (AddQuoteShortFormMessage.decode bytes).map fun (message, rest) => (.addQuoteShortFormMessage message, rest)
  else if tag = 74 then (AddQuoteLongFormMessage.decode bytes).map fun (message, rest) => (.addQuoteLongFormMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 88 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 117 then (OrderReplaceShortFormMessage.decode bytes).map fun (message, rest) => (.orderReplaceShortFormMessage message, rest)
  else if tag = 85 then (OrderReplaceLongFormMessage.decode bytes).map fun (message, rest) => (.orderReplaceLongFormMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 71 then (OrderChangeMessage.decode bytes).map fun (message, rest) => (.orderChangeMessage message, rest)
  else if tag = 107 then (QuoteReplaceShortFormMessage.decode bytes).map fun (message, rest) => (.quoteReplaceShortFormMessage message, rest)
  else if tag = 75 then (QuoteReplaceLongFormMessage.decode bytes).map fun (message, rest) => (.quoteReplaceLongFormMessage message, rest)
  else if tag = 89 then (QuoteDeleteMessage.decode bytes).map fun (message, rest) => (.quoteDeleteMessage message, rest)
  else if tag = 81 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 73 then (NetOrderImbalanceMessage.decode bytes).map fun (message, rest) => (.netOrderImbalanceMessage message, rest)
  else if tag = 77 then (EndOfReplaySequenceMessage.decode bytes).map fun (message, rest) => (.endOfReplaySequenceMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 87 := by
  unfold encode
  cases message.sequencedMessage with
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | derivativeDirectoryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, DerivativeDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TradingActionMessage.encode_length]
    omega
  | addOrderShortFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderShortFormMessage.encode_length]
    omega
  | addOrderLongFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderLongFormMessage.encode_length]
    omega
  | addQuoteShortFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddQuoteShortFormMessage.encode_length]
    omega
  | addQuoteLongFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddQuoteLongFormMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderCancelMessage.encode_length]
    omega
  | orderReplaceShortFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderReplaceShortFormMessage.encode_length]
    omega
  | orderReplaceLongFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderReplaceLongFormMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | orderChangeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderChangeMessage.encode_length]
    omega
  | quoteReplaceShortFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, QuoteReplaceShortFormMessage.encode_length]
    omega
  | quoteReplaceLongFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, QuoteReplaceLongFormMessage.encode_length]
    omega
  | quoteDeleteMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, QuoteDeleteMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | netOrderImbalanceMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, NetOrderImbalanceMessage.encode_length]
    omega
  | endOfReplaySequenceMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, EndOfReplaySequenceMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

end SequencedDataPacket

/-- Server Heartbeat Packet: 0 bytes -/
structure ServerHeartbeatPacket where
  deriving DecidableEq, Repr

namespace ServerHeartbeatPacket

def encode (_ : ServerHeartbeatPacket) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeatPacket × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeatPacket) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeatPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ServerHeartbeatPacket

/-- End Of Session Packet: 0 bytes -/
structure EndOfSessionPacket where
  deriving DecidableEq, Repr

namespace EndOfSessionPacket

def encode (_ : EndOfSessionPacket) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSessionPacket × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSessionPacket) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSessionPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end EndOfSessionPacket

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | serverHeartbeatPacket (message : ServerHeartbeatPacket) -- "H" 0x48
  | endOfSessionPacket (message : EndOfSessionPacket) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83
  | .serverHeartbeatPacket _ => 72
  | .endOfSessionPacket _ => 90

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .serverHeartbeatPacket message => ServerHeartbeatPacket.encode message
  | .endOfSessionPacket message => EndOfSessionPacket.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 87 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [encode, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [encode, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | serverHeartbeatPacket inner =>
    simp only [encode, ServerHeartbeatPacket.encode_length]
    omega
  | endOfSessionPacket inner =>
    simp only [encode, EndOfSessionPacket.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).map fun (message, rest) => (.loginAcceptedPacket message, rest)
  else if tag = 74 then (LoginRejectedPacket.decode bytes).map fun (message, rest) => (.loginRejectedPacket message, rest)
  else if tag = 83 then (SequencedDataPacket.decode bytes).map fun (message, rest) => (.sequencedDataPacket message, rest)
  else if tag = 72 then (ServerHeartbeatPacket.decode bytes).map fun (message, rest) => (.serverHeartbeatPacket message, rest)
  else if tag = 90 then (EndOfSessionPacket.decode bytes).map fun (message, rest) => (.endOfSessionPacket message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Soup Bin Tcp Packet -/
structure ServerSoupBinTcpPacket where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupBinTcpPacket

def encodeBody (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option (ServerSoupBinTcpPacket × List UInt8) := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let (serverPayload, bytes) ← ServerPayload.decode serverPacketType bytes
  pure ({ serverPayload }, bytes)

theorem decodeBody_encodeBody (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverPayload with
  | debugPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
    omega
  | serverHeartbeatPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeatPacket.encode_length]
    omega
  | endOfSessionPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, EndOfSessionPacket.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ServerSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ServerSoupBinTcpPacket × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ServerSoupBinTcpPacket

/-- Server Packet -/
structure ServerPacket where
  serverSoupBinTcpPacket : List ServerSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSoupBinTcpPacket.encode message.serverSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSoupBinTcpPacket ← decodeAll ServerSoupBinTcpPacket.decode bytes.length bytes
  pure { serverSoupBinTcpPacket }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.decode ServerSoupBinTcpPacket.decode_encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket _ (encodeMany_length_ge ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket), some_bind]
  rfl

end ServerPacket

end Omi.NasdaqNtxoptionsDepthofmarketItchV22Server
