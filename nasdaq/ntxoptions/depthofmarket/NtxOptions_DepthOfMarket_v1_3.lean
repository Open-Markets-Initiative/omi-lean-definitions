import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Depth Of Market v1.3

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNtxoptionsDepthofmarketItchV13

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4D, 0x45, 0x43]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfMarketHours -- Start Of Market Hours
  | endOfMarketHours -- End Of Market Hours
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
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x4D then .endOfMarketHours
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
  [0x43, 0x50]

inductive OptionType where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
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

/-- Options Closing Type: one byte code -/
def OptionsClosingType.codes : List UInt8 :=
  [0x4E, 0x4C]

inductive OptionsClosingType where
  | normal -- Normal
  | late -- Late
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionsClosingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionsClosingType

def toByte : OptionsClosingType → UInt8
  | .normal => 0x4E
  | .late => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionsClosingType :=
  if byte = 0x4E then .normal
  else .late

def ofByte (byte : UInt8) : OptionsClosingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionsClosingType) : ofByte value.toByte = value := by
  cases value with
  | normal => decide
  | late => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionsClosingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionsClosingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionsClosingType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionsClosingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionsClosingType

/-- Tradable: one byte code -/
def Tradable.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Tradable where
  | notTradable -- Not Tradable
  | isTradable -- Is Tradable
  | unlisted (byte : { byte : UInt8 // byte ∉ Tradable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tradable

def toByte : Tradable → UInt8
  | .notTradable => 0x4E
  | .isTradable => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tradable :=
  if byte = 0x4E then .notTradable
  else .isTradable

def ofByte (byte : UInt8) : Tradable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tradable) : ofByte value.toByte = value := by
  cases value with
  | notTradable => decide
  | isTradable => decide
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
  | everywhere -- Everywhere
  | scaled -- Scaled
  | pilot -- Pilot
  | unlisted (byte : { byte : UInt8 // byte ∉ Mpv.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Mpv

def toByte : Mpv → UInt8
  | .everywhere => 0x45
  | .scaled => 0x53
  | .pilot => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Mpv :=
  if byte = 0x45 then .everywhere
  else if byte = 0x53 then .scaled
  else .pilot

def ofByte (byte : UInt8) : Mpv :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Mpv) : ofByte value.toByte = value := by
  cases value with
  | everywhere => decide
  | scaled => decide
  | pilot => decide
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
  [0x48, 0x54, 0x42, 0x53, 0x59, 0x4E]

inductive CurrentTradingState where
  | halt -- Halt
  | trading -- Trading
  | buySideTradingSuspended -- Buy Side Trading Suspended
  | sellSideTradingSuspended -- Sell Side Trading Suspended
  | open_ -- Open
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .halt => 0x48
  | .trading => 0x54
  | .buySideTradingSuspended => 0x42
  | .sellSideTradingSuspended => 0x53
  | .open_ => 0x59
  | .closed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .halt
  else if byte = 0x54 then .trading
  else if byte = 0x42 then .buySideTradingSuspended
  else if byte = 0x53 then .sellSideTradingSuspended
  else if byte = 0x59 then .open_
  else .closed

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | halt => decide
  | trading => decide
  | buySideTradingSuspended => decide
  | sellSideTradingSuspended => decide
  | open_ => decide
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
  [0x42, 0x53]

inductive MarketSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketSide

def toByte : MarketSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : MarketSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
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

/-- Buy Sell Indicator: one byte code -/
def BuySellIndicator.codes : List UInt8 :=
  [0x42, 0x53]

inductive BuySellIndicator where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySellIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySellIndicator

def toByte : BuySellIndicator → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySellIndicator :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : BuySellIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySellIndicator) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuySellIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuySellIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuySellIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BuySellIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuySellIndicator

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x4F, 0x50]

inductive CrossType where
  | bxOpeningReopening -- Bx Opening Reopening
  | bxOpeningReopening_50 -- Bx Opening Reopening
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .bxOpeningReopening => 0x4F
  | .bxOpeningReopening_50 => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4F then .bxOpeningReopening
  else .bxOpeningReopening_50

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | bxOpeningReopening => decide
  | bxOpeningReopening_50 => decide
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

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x4F, 0x52, 0x49, 0x50]

inductive AuctionType where
  | opening -- Opening
  | reopening -- Reopening
  | exposure -- Exposure
  | priceImprovement -- Price Improvement
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .opening => 0x4F
  | .reopening => 0x52
  | .exposure => 0x49
  | .priceImprovement => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x4F then .opening
  else if byte = 0x52 then .reopening
  else if byte = 0x49 then .exposure
  else .priceImprovement

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | opening => decide
  | reopening => decide
  | exposure => decide
  | priceImprovement => decide
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
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceDirection

def toByte : ImbalanceDirection → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceDirection :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : ImbalanceDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceDirection) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
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

/-- Customer Firm Indicator: one byte code -/
def CustomerFirmIndicator.codes : List UInt8 :=
  [0x43, 0x46, 0x4D, 0x50, 0x42]

inductive CustomerFirmIndicator where
  | customer -- Customer
  | firmJoint -- Firm Joint
  | onfloor -- Onfloor
  | professional -- Professional
  | brokerDealerNonRegistered -- Broker Dealer Non Registered
  | unlisted (byte : { byte : UInt8 // byte ∉ CustomerFirmIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CustomerFirmIndicator

def toByte : CustomerFirmIndicator → UInt8
  | .customer => 0x43
  | .firmJoint => 0x46
  | .onfloor => 0x4D
  | .professional => 0x50
  | .brokerDealerNonRegistered => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CustomerFirmIndicator :=
  if byte = 0x43 then .customer
  else if byte = 0x46 then .firmJoint
  else if byte = 0x4D then .onfloor
  else if byte = 0x50 then .professional
  else .brokerDealerNonRegistered

def ofByte (byte : UInt8) : CustomerFirmIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CustomerFirmIndicator) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | firmJoint => decide
  | onfloor => decide
  | professional => decide
  | brokerDealerNonRegistered => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CustomerFirmIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CustomerFirmIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CustomerFirmIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CustomerFirmIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CustomerFirmIndicator

/-- Seconds Message: 4 bytes -/
structure SecondsMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace SecondsMessage

def encode (message : SecondsMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (SecondsMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : SecondsMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecondsMessage

/-- System Event Message: 5 bytes -/
structure SystemEventMessage where
  nanoseconds : BitVec 32
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (EventCode.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ nanoseconds, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 5 := by
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
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Base Reference Message: 12 bytes -/
structure BaseReferenceMessage where
  nanoseconds : BitVec 32
  baseReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace BaseReferenceMessage

def encode (message : BaseReferenceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.baseReferenceNumber)

def decode (bytes : List UInt8) : Option (BaseReferenceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (baseReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, baseReferenceNumber }, bytes)

@[simp] theorem encode_length (message : BaseReferenceMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BaseReferenceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BaseReferenceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BaseReferenceMessage

/-- Option Directory Message: 39 bytes -/
structure OptionDirectoryMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  securitySymbol : Alpha 6
  expirationYear : BitVec 8
  expirationMonth : BitVec 8
  expirationDate : BitVec 8
  explicitStrikePrice : BitVec 32
  optionType : OptionType
  source : BitVec 8
  underlyingSymbol : Alpha 13
  optionsClosingType : OptionsClosingType
  tradable : Tradable
  mpv : Mpv
  deriving DecidableEq, Repr

namespace OptionDirectoryMessage

def encode (message : OptionDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 1 message.expirationYear
    ++ (encodeUInt 1 message.expirationMonth
    ++ (encodeUInt 1 message.expirationDate
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (encodeUInt 1 message.source
    ++ (Alpha.encode message.underlyingSymbol
    ++ (OptionsClosingType.encode message.optionsClosingType
    ++ (Tradable.encode message.tradable
    ++ (Mpv.encode message.mpv))))))))))))

def decode (bytes : List UInt8) : Option (OptionDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 6 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  let (expirationMonth, bytes) ← decodeUInt 1 bytes
  let (expirationDate, bytes) ← decodeUInt 1 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (source, bytes) ← decodeUInt 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (optionsClosingType, bytes) ← OptionsClosingType.decode bytes
  let (tradable, bytes) ← Tradable.decode bytes
  let (mpv, bytes) ← Mpv.decode bytes
  pure ({ nanoseconds, optionId, securitySymbol, expirationYear, expirationMonth, expirationDate, explicitStrikePrice, optionType, source, underlyingSymbol, optionsClosingType, tradable, mpv }, bytes)

@[simp] theorem encode_length (message : OptionDirectoryMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, OptionsClosingType.encode_length, Tradable.encode_length, Mpv.encode_length]

theorem encode_length_pos (message : OptionDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionsClosingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tradable.decode_encode, some_bind]
  dsimp only
  rw [Mpv.decode_encode, some_bind]
  rfl

end OptionDirectoryMessage

/-- Trading Action Message: 9 bytes -/
structure TradingActionMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace TradingActionMessage

def encode (message : TradingActionMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (CurrentTradingState.encode message.currentTradingState))

def decode (bytes : List UInt8) : Option (TradingActionMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ nanoseconds, optionId, currentTradingState }, bytes)

@[simp] theorem encode_length (message : TradingActionMessage) : (encode message).length = 9 := by
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
  rw [CurrentTradingState.decode_encode, some_bind]
  rfl

end TradingActionMessage

/-- Option Open Message: 9 bytes -/
structure OptionOpenMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  openState : Alpha 1
  deriving DecidableEq, Repr

namespace OptionOpenMessage

def encode (message : OptionOpenMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.openState))

def decode (bytes : List UInt8) : Option (OptionOpenMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (openState, bytes) ← Alpha.decode 1 bytes
  pure ({ nanoseconds, optionId, openState }, bytes)

@[simp] theorem encode_length (message : OptionOpenMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OptionOpenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionOpenMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionOpenMessage

/-- Add Order Message Short Form: 17 bytes -/
structure AddOrderMessageShortForm where
  nanoseconds : BitVec 32
  orderReferenceNumberDelta : BitVec 32
  marketSide : MarketSide
  optionId : BitVec 32
  price : BitVec 16
  volume : BitVec 16
  deriving DecidableEq, Repr

namespace AddOrderMessageShortForm

def encode (message : AddOrderMessageShortForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderReferenceNumberDelta
    ++ (MarketSide.encode message.marketSide
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 2 message.price
    ++ (encodeUInt 2 message.volume)))))

def decode (bytes : List UInt8) : Option (AddOrderMessageShortForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (marketSide, bytes) ← MarketSide.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 2 bytes
  let (volume, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, orderReferenceNumberDelta, marketSide, optionId, price, volume }, bytes)

@[simp] theorem encode_length (message : AddOrderMessageShortForm) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, MarketSide.encode_length]

theorem encode_length_pos (message : AddOrderMessageShortForm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessageShortForm) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MarketSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessageShortForm

/-- Add Order Message Long Form: 21 bytes -/
structure AddOrderMessageLongForm where
  nanoseconds : BitVec 32
  orderReferenceNumberDelta : BitVec 32
  marketSide : MarketSide
  optionId : BitVec 32
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessageLongForm

def encode (message : AddOrderMessageLongForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderReferenceNumberDelta
    ++ (MarketSide.encode message.marketSide
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong)))))

def decode (bytes : List UInt8) : Option (AddOrderMessageLongForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (marketSide, bytes) ← MarketSide.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderReferenceNumberDelta, marketSide, optionId, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : AddOrderMessageLongForm) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, MarketSide.encode_length]

theorem encode_length_pos (message : AddOrderMessageLongForm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessageLongForm) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MarketSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessageLongForm

/-- Add Quote Message Short Form: 24 bytes -/
structure AddQuoteMessageShortForm where
  nanoseconds : BitVec 32
  bidReferenceNumberDelta : BitVec 32
  askReferenceNumberDelta : BitVec 32
  optionId : BitVec 32
  bidPrice : BitVec 16
  bidSize : BitVec 16
  askPrice : BitVec 16
  askSize : BitVec 16
  deriving DecidableEq, Repr

namespace AddQuoteMessageShortForm

def encode (message : AddQuoteMessageShortForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.bidReferenceNumberDelta
    ++ (encodeUInt 4 message.askReferenceNumberDelta
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 2 message.bidPrice
    ++ (encodeUInt 2 message.bidSize
    ++ (encodeUInt 2 message.askPrice
    ++ (encodeUInt 2 message.askSize)))))))

def decode (bytes : List UInt8) : Option (AddQuoteMessageShortForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (askReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (bidPrice, bytes) ← decodeUInt 2 bytes
  let (bidSize, bytes) ← decodeUInt 2 bytes
  let (askPrice, bytes) ← decodeUInt 2 bytes
  let (askSize, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, bidReferenceNumberDelta, askReferenceNumberDelta, optionId, bidPrice, bidSize, askPrice, askSize }, bytes)

@[simp] theorem encode_length (message : AddQuoteMessageShortForm) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AddQuoteMessageShortForm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddQuoteMessageShortForm) (rest : List UInt8) :
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

end AddQuoteMessageShortForm

/-- Add Quote Message Long Form: 32 bytes -/
structure AddQuoteMessageLongForm where
  nanoseconds : BitVec 32
  bidReferenceNumberDelta : BitVec 32
  askReferenceNumberDelta : BitVec 32
  optionId : BitVec 32
  bid : BitVec 32
  bidSizeLong : BitVec 32
  ask : BitVec 32
  askSizeLong : BitVec 32
  deriving DecidableEq, Repr

namespace AddQuoteMessageLongForm

def encode (message : AddQuoteMessageLongForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.bidReferenceNumberDelta
    ++ (encodeUInt 4 message.askReferenceNumberDelta
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.bid
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 4 message.ask
    ++ (encodeUInt 4 message.askSizeLong)))))))

def decode (bytes : List UInt8) : Option (AddQuoteMessageLongForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (askReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (bid, bytes) ← decodeUInt 4 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (ask, bytes) ← decodeUInt 4 bytes
  let (askSizeLong, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, bidReferenceNumberDelta, askReferenceNumberDelta, optionId, bid, bidSizeLong, ask, askSizeLong }, bytes)

@[simp] theorem encode_length (message : AddQuoteMessageLongForm) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AddQuoteMessageLongForm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddQuoteMessageLongForm) (rest : List UInt8) :
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

end AddQuoteMessageLongForm

/-- Single Side Executed Message: 20 bytes -/
structure SingleSideExecutedMessage where
  nanoseconds : BitVec 32
  referenceNumberDelta : BitVec 32
  executedContracts : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideExecutedMessage

def encode (message : SingleSideExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.referenceNumberDelta
    ++ (encodeUInt 4 message.executedContracts
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber))))

def decode (bytes : List UInt8) : Option (SingleSideExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (referenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (executedContracts, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, referenceNumberDelta, executedContracts, crossNumber, matchNumber }, bytes)

@[simp] theorem encode_length (message : SingleSideExecutedMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SingleSideExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideExecutedMessage) (rest : List UInt8) :
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

end SingleSideExecutedMessage

/-- Single Side Order Executed With Price Message: 25 bytes -/
structure SingleSideOrderExecutedWithPriceMessage where
  nanoseconds : BitVec 32
  referenceNumberDelta : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  printable : Printable
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideOrderExecutedWithPriceMessage

def encode (message : SingleSideOrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.referenceNumberDelta
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber
    ++ (Printable.encode message.printable
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong))))))

def decode (bytes : List UInt8) : Option (SingleSideOrderExecutedWithPriceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (referenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, referenceNumberDelta, crossNumber, matchNumber, printable := printable_, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : SingleSideOrderExecutedWithPriceMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length]

theorem encode_length_pos (message : SingleSideOrderExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideOrderExecutedWithPriceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleSideOrderExecutedWithPriceMessage

/-- Order Cancel Message: 12 bytes -/
structure OrderCancelMessage where
  nanoseconds : BitVec 32
  orderReferenceNumberDelta : BitVec 32
  cancelledContracts : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderReferenceNumberDelta
    ++ (encodeUInt 4 message.cancelledContracts))

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (cancelledContracts, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderReferenceNumberDelta, cancelledContracts }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 12 := by
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderCancelMessage

/-- Single Side Replace Message Short Form: 16 bytes -/
structure SingleSideReplaceMessageShortForm where
  nanoseconds : BitVec 32
  originalReferenceNumberDelta : BitVec 32
  newReferenceNumberDelta : BitVec 32
  price : BitVec 16
  volume : BitVec 16
  deriving DecidableEq, Repr

namespace SingleSideReplaceMessageShortForm

def encode (message : SingleSideReplaceMessageShortForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.originalReferenceNumberDelta
    ++ (encodeUInt 4 message.newReferenceNumberDelta
    ++ (encodeUInt 2 message.price
    ++ (encodeUInt 2 message.volume))))

def decode (bytes : List UInt8) : Option (SingleSideReplaceMessageShortForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (originalReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (newReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 2 bytes
  let (volume, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, originalReferenceNumberDelta, newReferenceNumberDelta, price, volume }, bytes)

@[simp] theorem encode_length (message : SingleSideReplaceMessageShortForm) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SingleSideReplaceMessageShortForm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideReplaceMessageShortForm) (rest : List UInt8) :
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

end SingleSideReplaceMessageShortForm

/-- Single Side Replace Message Long Form: 20 bytes -/
structure SingleSideReplaceMessageLongForm where
  nanoseconds : BitVec 32
  originalReferenceNumberDelta : BitVec 32
  newReferenceNumberDelta : BitVec 32
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideReplaceMessageLongForm

def encode (message : SingleSideReplaceMessageLongForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.originalReferenceNumberDelta
    ++ (encodeUInt 4 message.newReferenceNumberDelta
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong))))

def decode (bytes : List UInt8) : Option (SingleSideReplaceMessageLongForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (originalReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (newReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, originalReferenceNumberDelta, newReferenceNumberDelta, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : SingleSideReplaceMessageLongForm) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SingleSideReplaceMessageLongForm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideReplaceMessageLongForm) (rest : List UInt8) :
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

end SingleSideReplaceMessageLongForm

/-- Single Side Delete Message: 8 bytes -/
structure SingleSideDeleteMessage where
  nanoseconds : BitVec 32
  referenceNumberDelta : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideDeleteMessage

def encode (message : SingleSideDeleteMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.referenceNumberDelta)

def decode (bytes : List UInt8) : Option (SingleSideDeleteMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (referenceNumberDelta, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, referenceNumberDelta }, bytes)

@[simp] theorem encode_length (message : SingleSideDeleteMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SingleSideDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleSideDeleteMessage

/-- Single Side Update Message: 17 bytes -/
structure SingleSideUpdateMessage where
  nanoseconds : BitVec 32
  referenceNumberDelta : BitVec 32
  changeReason : ChangeReason
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideUpdateMessage

def encode (message : SingleSideUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.referenceNumberDelta
    ++ (ChangeReason.encode message.changeReason
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong))))

def decode (bytes : List UInt8) : Option (SingleSideUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (referenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (changeReason, bytes) ← ChangeReason.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, referenceNumberDelta, changeReason, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : SingleSideUpdateMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ChangeReason.encode_length]

theorem encode_length_pos (message : SingleSideUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end SingleSideUpdateMessage

/-- Quote Replace Message Short Form: 28 bytes -/
structure QuoteReplaceMessageShortForm where
  nanoseconds : BitVec 32
  originalBidReferenceNumberDelta : BitVec 32
  bidReferenceNumberDelta : BitVec 32
  originalAskReferenceNumberDelta : BitVec 32
  askReferenceDeltaNumber : BitVec 32
  bidPrice : BitVec 16
  bidSize : BitVec 16
  askPrice : BitVec 16
  askSize : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteReplaceMessageShortForm

def encode (message : QuoteReplaceMessageShortForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.originalBidReferenceNumberDelta
    ++ (encodeUInt 4 message.bidReferenceNumberDelta
    ++ (encodeUInt 4 message.originalAskReferenceNumberDelta
    ++ (encodeUInt 4 message.askReferenceDeltaNumber
    ++ (encodeUInt 2 message.bidPrice
    ++ (encodeUInt 2 message.bidSize
    ++ (encodeUInt 2 message.askPrice
    ++ (encodeUInt 2 message.askSize))))))))

def decode (bytes : List UInt8) : Option (QuoteReplaceMessageShortForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (originalBidReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (originalAskReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (askReferenceDeltaNumber, bytes) ← decodeUInt 4 bytes
  let (bidPrice, bytes) ← decodeUInt 2 bytes
  let (bidSize, bytes) ← decodeUInt 2 bytes
  let (askPrice, bytes) ← decodeUInt 2 bytes
  let (askSize, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, originalBidReferenceNumberDelta, bidReferenceNumberDelta, originalAskReferenceNumberDelta, askReferenceDeltaNumber, bidPrice, bidSize, askPrice, askSize }, bytes)

@[simp] theorem encode_length (message : QuoteReplaceMessageShortForm) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : QuoteReplaceMessageShortForm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteReplaceMessageShortForm) (rest : List UInt8) :
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

end QuoteReplaceMessageShortForm

/-- Quote Replace Message Long Form: 36 bytes -/
structure QuoteReplaceMessageLongForm where
  nanoseconds : BitVec 32
  originalBidReferenceNumberDelta : BitVec 32
  bidReferenceNumberDelta : BitVec 32
  originalAskReferenceNumberDelta : BitVec 32
  askReferenceDeltaNumber : BitVec 32
  bidPriceLong : BitVec 32
  bidSizeLong : BitVec 32
  askPriceLong : BitVec 32
  askSizeLong : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteReplaceMessageLongForm

def encode (message : QuoteReplaceMessageLongForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.originalBidReferenceNumberDelta
    ++ (encodeUInt 4 message.bidReferenceNumberDelta
    ++ (encodeUInt 4 message.originalAskReferenceNumberDelta
    ++ (encodeUInt 4 message.askReferenceDeltaNumber
    ++ (encodeUInt 4 message.bidPriceLong
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 4 message.askPriceLong
    ++ (encodeUInt 4 message.askSizeLong))))))))

def decode (bytes : List UInt8) : Option (QuoteReplaceMessageLongForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (originalBidReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (originalAskReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (askReferenceDeltaNumber, bytes) ← decodeUInt 4 bytes
  let (bidPriceLong, bytes) ← decodeUInt 4 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (askPriceLong, bytes) ← decodeUInt 4 bytes
  let (askSizeLong, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, originalBidReferenceNumberDelta, bidReferenceNumberDelta, originalAskReferenceNumberDelta, askReferenceDeltaNumber, bidPriceLong, bidSizeLong, askPriceLong, askSizeLong }, bytes)

@[simp] theorem encode_length (message : QuoteReplaceMessageLongForm) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : QuoteReplaceMessageLongForm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteReplaceMessageLongForm) (rest : List UInt8) :
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

end QuoteReplaceMessageLongForm

/-- Quote Delete Message: 12 bytes -/
structure QuoteDeleteMessage where
  nanoseconds : BitVec 32
  bidReferenceNumberDelta : BitVec 32
  askReferenceNumberDelta : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteDeleteMessage

def encode (message : QuoteDeleteMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.bidReferenceNumberDelta
    ++ (encodeUInt 4 message.askReferenceNumberDelta))

def decode (bytes : List UInt8) : Option (QuoteDeleteMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (askReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, bidReferenceNumberDelta, askReferenceNumberDelta }, bytes)

@[simp] theorem encode_length (message : QuoteDeleteMessage) : (encode message).length = 12 := by
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuoteDeleteMessage

/-- Block Delete Message: 10 bytes -/
structure BlockDeleteMessage where
  nanoseconds : BitVec 32
  totalNumberOfReferenceNumberDeltas : BitVec 16
  referenceNumberDeltan : BitVec 32
  deriving DecidableEq, Repr

namespace BlockDeleteMessage

def encode (message : BlockDeleteMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.totalNumberOfReferenceNumberDeltas
    ++ (encodeUInt 4 message.referenceNumberDeltan))

def decode (bytes : List UInt8) : Option (BlockDeleteMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (totalNumberOfReferenceNumberDeltas, bytes) ← decodeUInt 2 bytes
  let (referenceNumberDeltan, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, totalNumberOfReferenceNumberDeltas, referenceNumberDeltan }, bytes)

@[simp] theorem encode_length (message : BlockDeleteMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BlockDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BlockDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BlockDeleteMessage

/-- Non Auction Options Trade Message: 25 bytes -/
structure NonAuctionOptionsTradeMessage where
  nanoseconds : BitVec 32
  buySellIndicator : BuySellIndicator
  optionId : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace NonAuctionOptionsTradeMessage

def encode (message : NonAuctionOptionsTradeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong))))))

def decode (bytes : List UInt8) : Option (NonAuctionOptionsTradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, buySellIndicator, optionId, crossNumber, matchNumber, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : NonAuctionOptionsTradeMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BuySellIndicator.encode_length]

theorem encode_length_pos (message : NonAuctionOptionsTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NonAuctionOptionsTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
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

end NonAuctionOptionsTradeMessage

/-- Options Cross Trade Message: 25 bytes -/
structure OptionsCrossTradeMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  crossType : CrossType
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace OptionsCrossTradeMessage

def encode (message : OptionsCrossTradeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber
    ++ (CrossType.encode message.crossType
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong))))))

def decode (bytes : List UInt8) : Option (OptionsCrossTradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, optionId, crossNumber, matchNumber, crossType, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : OptionsCrossTradeMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CrossType.encode_length]

theorem encode_length_pos (message : OptionsCrossTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsCrossTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OptionsCrossTradeMessage

/-- Broken Trade Or Order Execution Message: 12 bytes -/
structure BrokenTradeOrOrderExecutionMessage where
  nanoseconds : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  deriving DecidableEq, Repr

namespace BrokenTradeOrOrderExecutionMessage

def encode (message : BrokenTradeOrOrderExecutionMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber))

def decode (bytes : List UInt8) : Option (BrokenTradeOrOrderExecutionMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, crossNumber, matchNumber }, bytes)

@[simp] theorem encode_length (message : BrokenTradeOrOrderExecutionMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BrokenTradeOrOrderExecutionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeOrOrderExecutionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BrokenTradeOrOrderExecutionMessage

/-- Net Order Imbalance Indicator Message: 30 bytes -/
structure NetOrderImbalanceIndicatorMessage where
  nanoseconds : BitVec 32
  auctionId : BitVec 32
  auctionType : AuctionType
  pairedContracts : BitVec 32
  imbalanceDirection : ImbalanceDirection
  optionId : BitVec 32
  imbalancePrice : BitVec 32
  imbalanceVolume : BitVec 32
  customerFirmIndicator : CustomerFirmIndicator
  reserved : BitVec 24
  deriving DecidableEq, Repr

namespace NetOrderImbalanceIndicatorMessage

def encode (message : NetOrderImbalanceIndicatorMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.auctionId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.pairedContracts
    ++ (ImbalanceDirection.encode message.imbalanceDirection
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.imbalancePrice
    ++ (encodeUInt 4 message.imbalanceVolume
    ++ (CustomerFirmIndicator.encode message.customerFirmIndicator
    ++ (encodeUInt 3 message.reserved)))))))))

def decode (bytes : List UInt8) : Option (NetOrderImbalanceIndicatorMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (pairedContracts, bytes) ← decodeUInt 4 bytes
  let (imbalanceDirection, bytes) ← ImbalanceDirection.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (imbalancePrice, bytes) ← decodeUInt 4 bytes
  let (imbalanceVolume, bytes) ← decodeUInt 4 bytes
  let (customerFirmIndicator, bytes) ← CustomerFirmIndicator.decode bytes
  let (reserved, bytes) ← decodeUInt 3 bytes
  pure ({ nanoseconds, auctionId, auctionType, pairedContracts, imbalanceDirection, optionId, imbalancePrice, imbalanceVolume, customerFirmIndicator, reserved }, bytes)

@[simp] theorem encode_length (message : NetOrderImbalanceIndicatorMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, AuctionType.encode_length, ImbalanceDirection.encode_length, CustomerFirmIndicator.encode_length]

theorem encode_length_pos (message : NetOrderImbalanceIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetOrderImbalanceIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CustomerFirmIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetOrderImbalanceIndicatorMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | secondsMessage (message : SecondsMessage) -- 'T' 0x54
  | systemEventMessage (message : SystemEventMessage) -- 'S' 0x53
  | baseReferenceMessage (message : BaseReferenceMessage) -- 'L' 0x4C
  | optionDirectoryMessage (message : OptionDirectoryMessage) -- 'R' 0x52
  | tradingActionMessage (message : TradingActionMessage) -- 'H' 0x48
  | optionOpenMessage (message : OptionOpenMessage) -- 'O' 0x4F
  | addOrderMessageShortForm (message : AddOrderMessageShortForm) -- 'a' 0x61
  | addOrderMessageLongForm (message : AddOrderMessageLongForm) -- 'A' 0x41
  | addQuoteMessageShortForm (message : AddQuoteMessageShortForm) -- 'j' 0x6A
  | addQuoteMessageLongForm (message : AddQuoteMessageLongForm) -- 'J' 0x4A
  | singleSideExecutedMessage (message : SingleSideExecutedMessage) -- 'E' 0x45
  | singleSideOrderExecutedWithPriceMessage (message : SingleSideOrderExecutedWithPriceMessage) -- 'C' 0x43
  | orderCancelMessage (message : OrderCancelMessage) -- 'X' 0x58
  | singleSideReplaceMessageShortForm (message : SingleSideReplaceMessageShortForm) -- 'u' 0x75
  | singleSideReplaceMessageLongForm (message : SingleSideReplaceMessageLongForm) -- 'U' 0x55
  | singleSideDeleteMessage (message : SingleSideDeleteMessage) -- 'D' 0x44
  | singleSideUpdateMessage (message : SingleSideUpdateMessage) -- 'G' 0x47
  | quoteReplaceMessageShortForm (message : QuoteReplaceMessageShortForm) -- 'k' 0x6B
  | quoteReplaceMessageLongForm (message : QuoteReplaceMessageLongForm) -- 'K' 0x4B
  | quoteDeleteMessage (message : QuoteDeleteMessage) -- 'Y' 0x59
  | blockDeleteMessage (message : BlockDeleteMessage) -- 'Z' 0x5A
  | nonAuctionOptionsTradeMessage (message : NonAuctionOptionsTradeMessage) -- 'P' 0x50
  | optionsCrossTradeMessage (message : OptionsCrossTradeMessage) -- 'Q' 0x51
  | brokenTradeOrOrderExecutionMessage (message : BrokenTradeOrOrderExecutionMessage) -- 'B' 0x42
  | netOrderImbalanceIndicatorMessage (message : NetOrderImbalanceIndicatorMessage) -- 'I' 0x49
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .secondsMessage _ => 84
  | .systemEventMessage _ => 83
  | .baseReferenceMessage _ => 76
  | .optionDirectoryMessage _ => 82
  | .tradingActionMessage _ => 72
  | .optionOpenMessage _ => 79
  | .addOrderMessageShortForm _ => 97
  | .addOrderMessageLongForm _ => 65
  | .addQuoteMessageShortForm _ => 106
  | .addQuoteMessageLongForm _ => 74
  | .singleSideExecutedMessage _ => 69
  | .singleSideOrderExecutedWithPriceMessage _ => 67
  | .orderCancelMessage _ => 88
  | .singleSideReplaceMessageShortForm _ => 117
  | .singleSideReplaceMessageLongForm _ => 85
  | .singleSideDeleteMessage _ => 68
  | .singleSideUpdateMessage _ => 71
  | .quoteReplaceMessageShortForm _ => 107
  | .quoteReplaceMessageLongForm _ => 75
  | .quoteDeleteMessage _ => 89
  | .blockDeleteMessage _ => 90
  | .nonAuctionOptionsTradeMessage _ => 80
  | .optionsCrossTradeMessage _ => 81
  | .brokenTradeOrOrderExecutionMessage _ => 66
  | .netOrderImbalanceIndicatorMessage _ => 73

def encode : Payload → List UInt8
  | .secondsMessage message => SecondsMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .baseReferenceMessage message => BaseReferenceMessage.encode message
  | .optionDirectoryMessage message => OptionDirectoryMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .optionOpenMessage message => OptionOpenMessage.encode message
  | .addOrderMessageShortForm message => AddOrderMessageShortForm.encode message
  | .addOrderMessageLongForm message => AddOrderMessageLongForm.encode message
  | .addQuoteMessageShortForm message => AddQuoteMessageShortForm.encode message
  | .addQuoteMessageLongForm message => AddQuoteMessageLongForm.encode message
  | .singleSideExecutedMessage message => SingleSideExecutedMessage.encode message
  | .singleSideOrderExecutedWithPriceMessage message => SingleSideOrderExecutedWithPriceMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .singleSideReplaceMessageShortForm message => SingleSideReplaceMessageShortForm.encode message
  | .singleSideReplaceMessageLongForm message => SingleSideReplaceMessageLongForm.encode message
  | .singleSideDeleteMessage message => SingleSideDeleteMessage.encode message
  | .singleSideUpdateMessage message => SingleSideUpdateMessage.encode message
  | .quoteReplaceMessageShortForm message => QuoteReplaceMessageShortForm.encode message
  | .quoteReplaceMessageLongForm message => QuoteReplaceMessageLongForm.encode message
  | .quoteDeleteMessage message => QuoteDeleteMessage.encode message
  | .blockDeleteMessage message => BlockDeleteMessage.encode message
  | .nonAuctionOptionsTradeMessage message => NonAuctionOptionsTradeMessage.encode message
  | .optionsCrossTradeMessage message => OptionsCrossTradeMessage.encode message
  | .brokenTradeOrOrderExecutionMessage message => BrokenTradeOrOrderExecutionMessage.encode message
  | .netOrderImbalanceIndicatorMessage message => NetOrderImbalanceIndicatorMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 39 := by
  cases message with
  | secondsMessage inner =>
    simp only [encode, SecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | baseReferenceMessage inner =>
    simp only [encode, BaseReferenceMessage.encode_length]
    omega
  | optionDirectoryMessage inner =>
    simp only [encode, OptionDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [encode, TradingActionMessage.encode_length]
    omega
  | optionOpenMessage inner =>
    simp only [encode, OptionOpenMessage.encode_length]
    omega
  | addOrderMessageShortForm inner =>
    simp only [encode, AddOrderMessageShortForm.encode_length]
    omega
  | addOrderMessageLongForm inner =>
    simp only [encode, AddOrderMessageLongForm.encode_length]
    omega
  | addQuoteMessageShortForm inner =>
    simp only [encode, AddQuoteMessageShortForm.encode_length]
    omega
  | addQuoteMessageLongForm inner =>
    simp only [encode, AddQuoteMessageLongForm.encode_length]
    omega
  | singleSideExecutedMessage inner =>
    simp only [encode, SingleSideExecutedMessage.encode_length]
    omega
  | singleSideOrderExecutedWithPriceMessage inner =>
    simp only [encode, SingleSideOrderExecutedWithPriceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [encode, OrderCancelMessage.encode_length]
    omega
  | singleSideReplaceMessageShortForm inner =>
    simp only [encode, SingleSideReplaceMessageShortForm.encode_length]
    omega
  | singleSideReplaceMessageLongForm inner =>
    simp only [encode, SingleSideReplaceMessageLongForm.encode_length]
    omega
  | singleSideDeleteMessage inner =>
    simp only [encode, SingleSideDeleteMessage.encode_length]
    omega
  | singleSideUpdateMessage inner =>
    simp only [encode, SingleSideUpdateMessage.encode_length]
    omega
  | quoteReplaceMessageShortForm inner =>
    simp only [encode, QuoteReplaceMessageShortForm.encode_length]
    omega
  | quoteReplaceMessageLongForm inner =>
    simp only [encode, QuoteReplaceMessageLongForm.encode_length]
    omega
  | quoteDeleteMessage inner =>
    simp only [encode, QuoteDeleteMessage.encode_length]
    omega
  | blockDeleteMessage inner =>
    simp only [encode, BlockDeleteMessage.encode_length]
    omega
  | nonAuctionOptionsTradeMessage inner =>
    simp only [encode, NonAuctionOptionsTradeMessage.encode_length]
    omega
  | optionsCrossTradeMessage inner =>
    simp only [encode, OptionsCrossTradeMessage.encode_length]
    omega
  | brokenTradeOrOrderExecutionMessage inner =>
    simp only [encode, BrokenTradeOrOrderExecutionMessage.encode_length]
    omega
  | netOrderImbalanceIndicatorMessage inner =>
    simp only [encode, NetOrderImbalanceIndicatorMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (SecondsMessage.decode bytes).map fun (message, rest) => (.secondsMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 76 then (BaseReferenceMessage.decode bytes).map fun (message, rest) => (.baseReferenceMessage message, rest)
  else if tag = 82 then (OptionDirectoryMessage.decode bytes).map fun (message, rest) => (.optionDirectoryMessage message, rest)
  else if tag = 72 then (TradingActionMessage.decode bytes).map fun (message, rest) => (.tradingActionMessage message, rest)
  else if tag = 79 then (OptionOpenMessage.decode bytes).map fun (message, rest) => (.optionOpenMessage message, rest)
  else if tag = 97 then (AddOrderMessageShortForm.decode bytes).map fun (message, rest) => (.addOrderMessageShortForm message, rest)
  else if tag = 65 then (AddOrderMessageLongForm.decode bytes).map fun (message, rest) => (.addOrderMessageLongForm message, rest)
  else if tag = 106 then (AddQuoteMessageShortForm.decode bytes).map fun (message, rest) => (.addQuoteMessageShortForm message, rest)
  else if tag = 74 then (AddQuoteMessageLongForm.decode bytes).map fun (message, rest) => (.addQuoteMessageLongForm message, rest)
  else if tag = 69 then (SingleSideExecutedMessage.decode bytes).map fun (message, rest) => (.singleSideExecutedMessage message, rest)
  else if tag = 67 then (SingleSideOrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.singleSideOrderExecutedWithPriceMessage message, rest)
  else if tag = 88 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 117 then (SingleSideReplaceMessageShortForm.decode bytes).map fun (message, rest) => (.singleSideReplaceMessageShortForm message, rest)
  else if tag = 85 then (SingleSideReplaceMessageLongForm.decode bytes).map fun (message, rest) => (.singleSideReplaceMessageLongForm message, rest)
  else if tag = 68 then (SingleSideDeleteMessage.decode bytes).map fun (message, rest) => (.singleSideDeleteMessage message, rest)
  else if tag = 71 then (SingleSideUpdateMessage.decode bytes).map fun (message, rest) => (.singleSideUpdateMessage message, rest)
  else if tag = 107 then (QuoteReplaceMessageShortForm.decode bytes).map fun (message, rest) => (.quoteReplaceMessageShortForm message, rest)
  else if tag = 75 then (QuoteReplaceMessageLongForm.decode bytes).map fun (message, rest) => (.quoteReplaceMessageLongForm message, rest)
  else if tag = 89 then (QuoteDeleteMessage.decode bytes).map fun (message, rest) => (.quoteDeleteMessage message, rest)
  else if tag = 90 then (BlockDeleteMessage.decode bytes).map fun (message, rest) => (.blockDeleteMessage message, rest)
  else if tag = 80 then (NonAuctionOptionsTradeMessage.decode bytes).map fun (message, rest) => (.nonAuctionOptionsTradeMessage message, rest)
  else if tag = 81 then (OptionsCrossTradeMessage.decode bytes).map fun (message, rest) => (.optionsCrossTradeMessage message, rest)
  else if tag = 66 then (BrokenTradeOrOrderExecutionMessage.decode bytes).map fun (message, rest) => (.brokenTradeOrOrderExecutionMessage message, rest)
  else if tag = 73 then (NetOrderImbalanceIndicatorMessage.decode bytes).map fun (message, rest) => (.netOrderImbalanceIndicatorMessage message, rest)
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
  | secondsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | baseReferenceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BaseReferenceMessage.encode_length]
    omega
  | optionDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OptionDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingActionMessage.encode_length]
    omega
  | optionOpenMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OptionOpenMessage.encode_length]
    omega
  | addOrderMessageShortForm inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMessageShortForm.encode_length]
    omega
  | addOrderMessageLongForm inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMessageLongForm.encode_length]
    omega
  | addQuoteMessageShortForm inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddQuoteMessageShortForm.encode_length]
    omega
  | addQuoteMessageLongForm inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddQuoteMessageLongForm.encode_length]
    omega
  | singleSideExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SingleSideExecutedMessage.encode_length]
    omega
  | singleSideOrderExecutedWithPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SingleSideOrderExecutedWithPriceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancelMessage.encode_length]
    omega
  | singleSideReplaceMessageShortForm inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SingleSideReplaceMessageShortForm.encode_length]
    omega
  | singleSideReplaceMessageLongForm inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SingleSideReplaceMessageLongForm.encode_length]
    omega
  | singleSideDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SingleSideDeleteMessage.encode_length]
    omega
  | singleSideUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SingleSideUpdateMessage.encode_length]
    omega
  | quoteReplaceMessageShortForm inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteReplaceMessageShortForm.encode_length]
    omega
  | quoteReplaceMessageLongForm inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteReplaceMessageLongForm.encode_length]
    omega
  | quoteDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteDeleteMessage.encode_length]
    omega
  | blockDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BlockDeleteMessage.encode_length]
    omega
  | nonAuctionOptionsTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NonAuctionOptionsTradeMessage.encode_length]
    omega
  | optionsCrossTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OptionsCrossTradeMessage.encode_length]
    omega
  | brokenTradeOrOrderExecutionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BrokenTradeOrOrderExecutionMessage.encode_length]
    omega
  | netOrderImbalanceIndicatorMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NetOrderImbalanceIndicatorMessage.encode_length]
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

end Omi.NasdaqNtxoptionsDepthofmarketItchV13
