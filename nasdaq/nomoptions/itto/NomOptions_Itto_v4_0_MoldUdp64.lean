import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Itch To Trade Options v4.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNomoptionsIttoItchV40MoldUdp64

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
  [0x48, 0x54, 0x42, 0x53]

inductive CurrentTradingState where
  | halt -- Halt
  | trading -- Trading
  | buySideTradingSuspended -- Buy Side Trading Suspended
  | sellSideTradingSuspended -- Sell Side Trading Suspended
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .halt => 0x48
  | .trading => 0x54
  | .buySideTradingSuspended => 0x42
  | .sellSideTradingSuspended => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .halt
  else if byte = 0x54 then .trading
  else if byte = 0x42 then .buySideTradingSuspended
  else .sellSideTradingSuspended

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | halt => decide
  | trading => decide
  | buySideTradingSuspended => decide
  | sellSideTradingSuspended => decide
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

/-- Open State: one byte code -/
def OpenState.codes : List UInt8 :=
  [0x59, 0x4E]

inductive OpenState where
  | open_ -- Open
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenState

def toByte : OpenState → UInt8
  | .open_ => 0x59
  | .closed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenState :=
  if byte = 0x59 then .open_
  else .closed

def ofByte (byte : UInt8) : OpenState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenState) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | closed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenState

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
  | nasdaqOpeningReopening -- Nasdaq Opening Reopening
  | priceImprovement -- Price Improvement
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .nasdaqOpeningReopening => 0x4F
  | .priceImprovement => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4F then .nasdaqOpeningReopening
  else .priceImprovement

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | nasdaqOpeningReopening => decide
  | priceImprovement => decide
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
  [0x4F, 0x52, 0x50, 0x49]

inductive AuctionType where
  | opening -- Opening
  | reopening -- Reopening
  | priceImprovement -- Price Improvement
  | exposure -- Exposure
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .opening => 0x4F
  | .reopening => 0x52
  | .priceImprovement => 0x50
  | .exposure => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x4F then .opening
  else if byte = 0x52 then .reopening
  else if byte = 0x50 then .priceImprovement
  else .exposure

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | opening => decide
  | reopening => decide
  | priceImprovement => decide
  | exposure => decide
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

/-- System Event Message: 9 bytes -/
structure SystemEventMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (EventCode.encode message.eventCode))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ trackingNumber, timestamp, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 9 := by
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

/-- Options Directory Message: 43 bytes -/
structure OptionsDirectoryMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
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

namespace OptionsDirectoryMessage

def encode (message : OptionsDirectoryMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
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
    ++ (Mpv.encode message.mpv)))))))))))))

def decode (bytes : List UInt8) : Option (OptionsDirectoryMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
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
  pure ({ trackingNumber, timestamp, optionId, securitySymbol, expirationYear, expirationMonth, expirationDate, explicitStrikePrice, optionType, source, underlyingSymbol, optionsClosingType, tradable, mpv }, bytes)

@[simp] theorem encode_length (message : OptionsDirectoryMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, OptionsClosingType.encode_length, Tradable.encode_length, Mpv.encode_length]

theorem encode_length_pos (message : OptionsDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsDirectoryMessage) (rest : List UInt8) :
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

end OptionsDirectoryMessage

/-- Trading Action Message: 13 bytes -/
structure TradingActionMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  optionId : BitVec 32
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace TradingActionMessage

def encode (message : TradingActionMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (CurrentTradingState.encode message.currentTradingState)))

def decode (bytes : List UInt8) : Option (TradingActionMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ trackingNumber, timestamp, optionId, currentTradingState }, bytes)

@[simp] theorem encode_length (message : TradingActionMessage) : (encode message).length = 13 := by
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

/-- Security Open Message: 13 bytes -/
structure SecurityOpenMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  optionId : BitVec 32
  openState : OpenState
  deriving DecidableEq, Repr

namespace SecurityOpenMessage

def encode (message : SecurityOpenMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (OpenState.encode message.openState)))

def decode (bytes : List UInt8) : Option (SecurityOpenMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (openState, bytes) ← OpenState.decode bytes
  pure ({ trackingNumber, timestamp, optionId, openState }, bytes)

@[simp] theorem encode_length (message : SecurityOpenMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OpenState.encode_length]

theorem encode_length_pos (message : SecurityOpenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityOpenMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OpenState.decode_encode, some_bind]
  rfl

end SecurityOpenMessage

/-- Add Order Message Short Message Form: 25 bytes -/
structure AddOrderMessageShortMessageForm where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  orderReferenceNumber : BitVec 64
  marketSide : MarketSide
  optionId : BitVec 32
  priceShort : BitVec 16
  volumeShort : BitVec 16
  deriving DecidableEq, Repr

namespace AddOrderMessageShortMessageForm

def encode (message : AddOrderMessageShortMessageForm) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (MarketSide.encode message.marketSide
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 2 message.priceShort
    ++ (encodeUInt 2 message.volumeShort))))))

def decode (bytes : List UInt8) : Option (AddOrderMessageShortMessageForm × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (marketSide, bytes) ← MarketSide.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (priceShort, bytes) ← decodeUInt 2 bytes
  let (volumeShort, bytes) ← decodeUInt 2 bytes
  pure ({ trackingNumber, timestamp, orderReferenceNumber, marketSide, optionId, priceShort, volumeShort }, bytes)

@[simp] theorem encode_length (message : AddOrderMessageShortMessageForm) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, MarketSide.encode_length]

theorem encode_length_pos (message : AddOrderMessageShortMessageForm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessageShortMessageForm) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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

end AddOrderMessageShortMessageForm

/-- Add Order Message Long Form Message: 29 bytes -/
structure AddOrderMessageLongFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  orderReferenceNumber : BitVec 64
  marketSide : MarketSide
  optionId : BitVec 32
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessageLongFormMessage

def encode (message : AddOrderMessageLongFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (MarketSide.encode message.marketSide
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong))))))

def decode (bytes : List UInt8) : Option (AddOrderMessageLongFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (marketSide, bytes) ← MarketSide.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, orderReferenceNumber, marketSide, optionId, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : AddOrderMessageLongFormMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, MarketSide.encode_length]

theorem encode_length_pos (message : AddOrderMessageLongFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessageLongFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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

end AddOrderMessageLongFormMessage

/-- Add Quote Message Short Form Message: 36 bytes -/
structure AddQuoteMessageShortFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  bidReferenceNumber : BitVec 64
  askReferenceNumber : BitVec 64
  optionId : BitVec 32
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  askPriceShort : BitVec 16
  askSizeShort : BitVec 16
  deriving DecidableEq, Repr

namespace AddQuoteMessageShortFormMessage

def encode (message : AddQuoteMessageShortFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.bidReferenceNumber
    ++ (encodeUInt 8 message.askReferenceNumber
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 2 message.bidPriceShort
    ++ (encodeUInt 2 message.bidSizeShort
    ++ (encodeUInt 2 message.askPriceShort
    ++ (encodeUInt 2 message.askSizeShort))))))))

def decode (bytes : List UInt8) : Option (AddQuoteMessageShortFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (bidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (askReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (bidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bidSizeShort, bytes) ← decodeUInt 2 bytes
  let (askPriceShort, bytes) ← decodeUInt 2 bytes
  let (askSizeShort, bytes) ← decodeUInt 2 bytes
  pure ({ trackingNumber, timestamp, bidReferenceNumber, askReferenceNumber, optionId, bidPriceShort, bidSizeShort, askPriceShort, askSizeShort }, bytes)

@[simp] theorem encode_length (message : AddQuoteMessageShortFormMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AddQuoteMessageShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddQuoteMessageShortFormMessage) (rest : List UInt8) :
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

end AddQuoteMessageShortFormMessage

/-- Add Quote Message Long Form Message: 44 bytes -/
structure AddQuoteMessageLongFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  bidReferenceNumber : BitVec 64
  askReferenceNumber : BitVec 64
  optionId : BitVec 32
  bid : BitVec 32
  bidSizeLong : BitVec 32
  ask : BitVec 32
  askSizeLong : BitVec 32
  deriving DecidableEq, Repr

namespace AddQuoteMessageLongFormMessage

def encode (message : AddQuoteMessageLongFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.bidReferenceNumber
    ++ (encodeUInt 8 message.askReferenceNumber
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.bid
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 4 message.ask
    ++ (encodeUInt 4 message.askSizeLong))))))))

def decode (bytes : List UInt8) : Option (AddQuoteMessageLongFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (bidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (askReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (bid, bytes) ← decodeUInt 4 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (ask, bytes) ← decodeUInt 4 bytes
  let (askSizeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, bidReferenceNumber, askReferenceNumber, optionId, bid, bidSizeLong, ask, askSizeLong }, bytes)

@[simp] theorem encode_length (message : AddQuoteMessageLongFormMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AddQuoteMessageLongFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddQuoteMessageLongFormMessage) (rest : List UInt8) :
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

end AddQuoteMessageLongFormMessage

/-- Single Side Executed Message: 28 bytes -/
structure SingleSideExecutedMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  referenceNumber : BitVec 64
  executedContracts : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideExecutedMessage

def encode (message : SingleSideExecutedMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.referenceNumber
    ++ (encodeUInt 4 message.executedContracts
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber)))))

def decode (bytes : List UInt8) : Option (SingleSideExecutedMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (referenceNumber, bytes) ← decodeUInt 8 bytes
  let (executedContracts, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, referenceNumber, executedContracts, crossNumber, matchNumber }, bytes)

@[simp] theorem encode_length (message : SingleSideExecutedMessage) : (encode message).length = 28 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleSideExecutedMessage

/-- Single Side Executed With Price Message: 33 bytes -/
structure SingleSideExecutedWithPriceMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  referenceNumber : BitVec 64
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  printable : Printable
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideExecutedWithPriceMessage

def encode (message : SingleSideExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.referenceNumber
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber
    ++ (Printable.encode message.printable
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong)))))))

def decode (bytes : List UInt8) : Option (SingleSideExecutedWithPriceMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (referenceNumber, bytes) ← decodeUInt 8 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, referenceNumber, crossNumber, matchNumber, printable := printable_, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : SingleSideExecutedWithPriceMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length]

theorem encode_length_pos (message : SingleSideExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideExecutedWithPriceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleSideExecutedWithPriceMessage

/-- Order Cancel Message: 20 bytes -/
structure OrderCancelMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  orderReferenceNumber : BitVec 64
  cancelledContracts : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeUInt 4 message.cancelledContracts)))

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (cancelledContracts, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, orderReferenceNumber, cancelledContracts }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 20 := by
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderCancelMessage

/-- Single Side Replace Message Short Form: 28 bytes -/
structure SingleSideReplaceMessageShortForm where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  originalReferenceNumber : BitVec 64
  newReferenceNumber : BitVec 64
  priceShort : BitVec 16
  volumeShort : BitVec 16
  deriving DecidableEq, Repr

namespace SingleSideReplaceMessageShortForm

def encode (message : SingleSideReplaceMessageShortForm) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.originalReferenceNumber
    ++ (encodeUInt 8 message.newReferenceNumber
    ++ (encodeUInt 2 message.priceShort
    ++ (encodeUInt 2 message.volumeShort)))))

def decode (bytes : List UInt8) : Option (SingleSideReplaceMessageShortForm × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (originalReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (newReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (priceShort, bytes) ← decodeUInt 2 bytes
  let (volumeShort, bytes) ← decodeUInt 2 bytes
  pure ({ trackingNumber, timestamp, originalReferenceNumber, newReferenceNumber, priceShort, volumeShort }, bytes)

@[simp] theorem encode_length (message : SingleSideReplaceMessageShortForm) : (encode message).length = 28 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleSideReplaceMessageShortForm

/-- Single Side Replace Message Long Form: 32 bytes -/
structure SingleSideReplaceMessageLongForm where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  originalReferenceNumber : BitVec 64
  newReferenceNumber : BitVec 64
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideReplaceMessageLongForm

def encode (message : SingleSideReplaceMessageLongForm) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.originalReferenceNumber
    ++ (encodeUInt 8 message.newReferenceNumber
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong)))))

def decode (bytes : List UInt8) : Option (SingleSideReplaceMessageLongForm × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (originalReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (newReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, originalReferenceNumber, newReferenceNumber, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : SingleSideReplaceMessageLongForm) : (encode message).length = 32 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleSideReplaceMessageLongForm

/-- Single Side Delete Message: 16 bytes -/
structure SingleSideDeleteMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  referenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace SingleSideDeleteMessage

def encode (message : SingleSideDeleteMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.referenceNumber))

def decode (bytes : List UInt8) : Option (SingleSideDeleteMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (referenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ trackingNumber, timestamp, referenceNumber }, bytes)

@[simp] theorem encode_length (message : SingleSideDeleteMessage) : (encode message).length = 16 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleSideDeleteMessage

/-- Single Side Change Message: 25 bytes -/
structure SingleSideChangeMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  referenceNumber : BitVec 64
  changeReason : ChangeReason
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideChangeMessage

def encode (message : SingleSideChangeMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.referenceNumber
    ++ (ChangeReason.encode message.changeReason
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong)))))

def decode (bytes : List UInt8) : Option (SingleSideChangeMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (referenceNumber, bytes) ← decodeUInt 8 bytes
  let (changeReason, bytes) ← ChangeReason.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, referenceNumber, changeReason, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : SingleSideChangeMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ChangeReason.encode_length]

theorem encode_length_pos (message : SingleSideChangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideChangeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end SingleSideChangeMessage

/-- Quote Replace Message Short Form: 48 bytes -/
structure QuoteReplaceMessageShortForm where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  originalBidReferenceNumber : BitVec 64
  bidReferenceNumber : BitVec 64
  originalAskReferenceNumber : BitVec 64
  askReferenceNumber : BitVec 64
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  askPriceShort : BitVec 16
  askSizeShort : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteReplaceMessageShortForm

def encode (message : QuoteReplaceMessageShortForm) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.originalBidReferenceNumber
    ++ (encodeUInt 8 message.bidReferenceNumber
    ++ (encodeUInt 8 message.originalAskReferenceNumber
    ++ (encodeUInt 8 message.askReferenceNumber
    ++ (encodeUInt 2 message.bidPriceShort
    ++ (encodeUInt 2 message.bidSizeShort
    ++ (encodeUInt 2 message.askPriceShort
    ++ (encodeUInt 2 message.askSizeShort)))))))))

def decode (bytes : List UInt8) : Option (QuoteReplaceMessageShortForm × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (originalBidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (bidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (originalAskReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (askReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (bidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bidSizeShort, bytes) ← decodeUInt 2 bytes
  let (askPriceShort, bytes) ← decodeUInt 2 bytes
  let (askSizeShort, bytes) ← decodeUInt 2 bytes
  pure ({ trackingNumber, timestamp, originalBidReferenceNumber, bidReferenceNumber, originalAskReferenceNumber, askReferenceNumber, bidPriceShort, bidSizeShort, askPriceShort, askSizeShort }, bytes)

@[simp] theorem encode_length (message : QuoteReplaceMessageShortForm) : (encode message).length = 48 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuoteReplaceMessageShortForm

/-- Quote Replace Message Long Form: 56 bytes -/
structure QuoteReplaceMessageLongForm where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  originalBidReferenceNumber : BitVec 64
  bidReferenceNumber : BitVec 64
  originalAskReferenceNumber : BitVec 64
  askReferenceNumber : BitVec 64
  bidPriceLong : BitVec 32
  bidSizeLong : BitVec 32
  askPriceLong : BitVec 32
  askSizeLong : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteReplaceMessageLongForm

def encode (message : QuoteReplaceMessageLongForm) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.originalBidReferenceNumber
    ++ (encodeUInt 8 message.bidReferenceNumber
    ++ (encodeUInt 8 message.originalAskReferenceNumber
    ++ (encodeUInt 8 message.askReferenceNumber
    ++ (encodeUInt 4 message.bidPriceLong
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 4 message.askPriceLong
    ++ (encodeUInt 4 message.askSizeLong)))))))))

def decode (bytes : List UInt8) : Option (QuoteReplaceMessageLongForm × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (originalBidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (bidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (originalAskReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (askReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (bidPriceLong, bytes) ← decodeUInt 4 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (askPriceLong, bytes) ← decodeUInt 4 bytes
  let (askSizeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, originalBidReferenceNumber, bidReferenceNumber, originalAskReferenceNumber, askReferenceNumber, bidPriceLong, bidSizeLong, askPriceLong, askSizeLong }, bytes)

@[simp] theorem encode_length (message : QuoteReplaceMessageLongForm) : (encode message).length = 56 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuoteReplaceMessageLongForm

/-- Quote Delete Message: 24 bytes -/
structure QuoteDeleteMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  bidReferenceNumber : BitVec 64
  askReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteDeleteMessage

def encode (message : QuoteDeleteMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.bidReferenceNumber
    ++ (encodeUInt 8 message.askReferenceNumber)))

def decode (bytes : List UInt8) : Option (QuoteDeleteMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (bidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (askReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ trackingNumber, timestamp, bidReferenceNumber, askReferenceNumber }, bytes)

@[simp] theorem encode_length (message : QuoteDeleteMessage) : (encode message).length = 24 := by
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuoteDeleteMessage

/-- Options Trade Messages Non Auction: 29 bytes -/
structure OptionsTradeMessagesNonAuction where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  buySellIndicator : BuySellIndicator
  optionId : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace OptionsTradeMessagesNonAuction

def encode (message : OptionsTradeMessagesNonAuction) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong)))))))

def decode (bytes : List UInt8) : Option (OptionsTradeMessagesNonAuction × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, buySellIndicator, optionId, crossNumber, matchNumber, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : OptionsTradeMessagesNonAuction) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BuySellIndicator.encode_length]

theorem encode_length_pos (message : OptionsTradeMessagesNonAuction) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsTradeMessagesNonAuction) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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

end OptionsTradeMessagesNonAuction

/-- Options Cross Trade Message: 29 bytes -/
structure OptionsCrossTradeMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  optionId : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  crossType : CrossType
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace OptionsCrossTradeMessage

def encode (message : OptionsCrossTradeMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber
    ++ (CrossType.encode message.crossType
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong)))))))

def decode (bytes : List UInt8) : Option (OptionsCrossTradeMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, optionId, crossNumber, matchNumber, crossType, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : OptionsCrossTradeMessage) : (encode message).length = 29 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OptionsCrossTradeMessage

/-- Broken Trade Order Executed Message: 16 bytes -/
structure BrokenTradeOrderExecutedMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  deriving DecidableEq, Repr

namespace BrokenTradeOrderExecutedMessage

def encode (message : BrokenTradeOrderExecutedMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber)))

def decode (bytes : List UInt8) : Option (BrokenTradeOrderExecutedMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, crossNumber, matchNumber }, bytes)

@[simp] theorem encode_length (message : BrokenTradeOrderExecutedMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BrokenTradeOrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeOrderExecutedMessage) (rest : List UInt8) :
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

end BrokenTradeOrderExecutedMessage

/-- Noii Message: 34 bytes -/
structure NoiiMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  auctionId : BitVec 32
  auctionType : AuctionType
  pairedContracts : BitVec 32
  imbalanceDirection : ImbalanceDirection
  optionId : BitVec 32
  imbalancePrice : BitVec 32
  imbalanceVolume : BitVec 32
  customerFirmIndicator : CustomerFirmIndicator
  reserved3 : Alpha 3
  deriving DecidableEq, Repr

namespace NoiiMessage

def encode (message : NoiiMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.auctionId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.pairedContracts
    ++ (ImbalanceDirection.encode message.imbalanceDirection
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.imbalancePrice
    ++ (encodeUInt 4 message.imbalanceVolume
    ++ (CustomerFirmIndicator.encode message.customerFirmIndicator
    ++ (Alpha.encode message.reserved3))))))))))

def decode (bytes : List UInt8) : Option (NoiiMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (pairedContracts, bytes) ← decodeUInt 4 bytes
  let (imbalanceDirection, bytes) ← ImbalanceDirection.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (imbalancePrice, bytes) ← decodeUInt 4 bytes
  let (imbalanceVolume, bytes) ← decodeUInt 4 bytes
  let (customerFirmIndicator, bytes) ← CustomerFirmIndicator.decode bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  pure ({ trackingNumber, timestamp, auctionId, auctionType, pairedContracts, imbalanceDirection, optionId, imbalancePrice, imbalanceVolume, customerFirmIndicator, reserved3 }, bytes)

@[simp] theorem encode_length (message : NoiiMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, AuctionType.encode_length, ImbalanceDirection.encode_length, CustomerFirmIndicator.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : NoiiMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NoiiMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CustomerFirmIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NoiiMessage

/-- Any Udp Payload, selected by Message Type -/
inductive UdpPayload where
  | systemEventMessage (message : SystemEventMessage) -- 'S' 0x53
  | optionsDirectoryMessage (message : OptionsDirectoryMessage) -- 'R' 0x52
  | tradingActionMessage (message : TradingActionMessage) -- 'H' 0x48
  | securityOpenMessage (message : SecurityOpenMessage) -- 'O' 0x4F
  | addOrderMessageShortMessageForm (message : AddOrderMessageShortMessageForm) -- 'a' 0x61
  | addOrderMessageLongFormMessage (message : AddOrderMessageLongFormMessage) -- 'A' 0x41
  | addQuoteMessageShortFormMessage (message : AddQuoteMessageShortFormMessage) -- 'j' 0x6A
  | addQuoteMessageLongFormMessage (message : AddQuoteMessageLongFormMessage) -- 'J' 0x4A
  | singleSideExecutedMessage (message : SingleSideExecutedMessage) -- 'E' 0x45
  | singleSideExecutedWithPriceMessage (message : SingleSideExecutedWithPriceMessage) -- 'C' 0x43
  | orderCancelMessage (message : OrderCancelMessage) -- 'X' 0x58
  | singleSideReplaceMessageShortForm (message : SingleSideReplaceMessageShortForm) -- 'u' 0x75
  | singleSideReplaceMessageLongForm (message : SingleSideReplaceMessageLongForm) -- 'U' 0x55
  | singleSideDeleteMessage (message : SingleSideDeleteMessage) -- 'D' 0x44
  | singleSideChangeMessage (message : SingleSideChangeMessage) -- 'G' 0x47
  | quoteReplaceMessageShortForm (message : QuoteReplaceMessageShortForm) -- 'k' 0x6B
  | quoteReplaceMessageLongForm (message : QuoteReplaceMessageLongForm) -- 'K' 0x4B
  | quoteDeleteMessage (message : QuoteDeleteMessage) -- 'Y' 0x59
  | optionsTradeMessagesNonAuction (message : OptionsTradeMessagesNonAuction) -- 'P' 0x50
  | optionsCrossTradeMessage (message : OptionsCrossTradeMessage) -- 'Q' 0x51
  | brokenTradeOrderExecutedMessage (message : BrokenTradeOrderExecutedMessage) -- 'B' 0x42
  | noiiMessage (message : NoiiMessage) -- 'I' 0x49
  deriving DecidableEq, Repr

namespace UdpPayload

/-- The Message Type each message is sent under -/
def tag : UdpPayload → BitVec 8
  | .systemEventMessage _ => 83
  | .optionsDirectoryMessage _ => 82
  | .tradingActionMessage _ => 72
  | .securityOpenMessage _ => 79
  | .addOrderMessageShortMessageForm _ => 97
  | .addOrderMessageLongFormMessage _ => 65
  | .addQuoteMessageShortFormMessage _ => 106
  | .addQuoteMessageLongFormMessage _ => 74
  | .singleSideExecutedMessage _ => 69
  | .singleSideExecutedWithPriceMessage _ => 67
  | .orderCancelMessage _ => 88
  | .singleSideReplaceMessageShortForm _ => 117
  | .singleSideReplaceMessageLongForm _ => 85
  | .singleSideDeleteMessage _ => 68
  | .singleSideChangeMessage _ => 71
  | .quoteReplaceMessageShortForm _ => 107
  | .quoteReplaceMessageLongForm _ => 75
  | .quoteDeleteMessage _ => 89
  | .optionsTradeMessagesNonAuction _ => 80
  | .optionsCrossTradeMessage _ => 81
  | .brokenTradeOrderExecutedMessage _ => 66
  | .noiiMessage _ => 73

def encode : UdpPayload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .optionsDirectoryMessage message => OptionsDirectoryMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .securityOpenMessage message => SecurityOpenMessage.encode message
  | .addOrderMessageShortMessageForm message => AddOrderMessageShortMessageForm.encode message
  | .addOrderMessageLongFormMessage message => AddOrderMessageLongFormMessage.encode message
  | .addQuoteMessageShortFormMessage message => AddQuoteMessageShortFormMessage.encode message
  | .addQuoteMessageLongFormMessage message => AddQuoteMessageLongFormMessage.encode message
  | .singleSideExecutedMessage message => SingleSideExecutedMessage.encode message
  | .singleSideExecutedWithPriceMessage message => SingleSideExecutedWithPriceMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .singleSideReplaceMessageShortForm message => SingleSideReplaceMessageShortForm.encode message
  | .singleSideReplaceMessageLongForm message => SingleSideReplaceMessageLongForm.encode message
  | .singleSideDeleteMessage message => SingleSideDeleteMessage.encode message
  | .singleSideChangeMessage message => SingleSideChangeMessage.encode message
  | .quoteReplaceMessageShortForm message => QuoteReplaceMessageShortForm.encode message
  | .quoteReplaceMessageLongForm message => QuoteReplaceMessageLongForm.encode message
  | .quoteDeleteMessage message => QuoteDeleteMessage.encode message
  | .optionsTradeMessagesNonAuction message => OptionsTradeMessagesNonAuction.encode message
  | .optionsCrossTradeMessage message => OptionsCrossTradeMessage.encode message
  | .brokenTradeOrderExecutedMessage message => BrokenTradeOrderExecutedMessage.encode message
  | .noiiMessage message => NoiiMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UdpPayload) : (encode message).length ≤ 56 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | optionsDirectoryMessage inner =>
    simp only [encode, OptionsDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [encode, TradingActionMessage.encode_length]
    omega
  | securityOpenMessage inner =>
    simp only [encode, SecurityOpenMessage.encode_length]
    omega
  | addOrderMessageShortMessageForm inner =>
    simp only [encode, AddOrderMessageShortMessageForm.encode_length]
    omega
  | addOrderMessageLongFormMessage inner =>
    simp only [encode, AddOrderMessageLongFormMessage.encode_length]
    omega
  | addQuoteMessageShortFormMessage inner =>
    simp only [encode, AddQuoteMessageShortFormMessage.encode_length]
    omega
  | addQuoteMessageLongFormMessage inner =>
    simp only [encode, AddQuoteMessageLongFormMessage.encode_length]
    omega
  | singleSideExecutedMessage inner =>
    simp only [encode, SingleSideExecutedMessage.encode_length]
    omega
  | singleSideExecutedWithPriceMessage inner =>
    simp only [encode, SingleSideExecutedWithPriceMessage.encode_length]
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
  | singleSideChangeMessage inner =>
    simp only [encode, SingleSideChangeMessage.encode_length]
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
  | optionsTradeMessagesNonAuction inner =>
    simp only [encode, OptionsTradeMessagesNonAuction.encode_length]
    omega
  | optionsCrossTradeMessage inner =>
    simp only [encode, OptionsCrossTradeMessage.encode_length]
    omega
  | brokenTradeOrderExecutedMessage inner =>
    simp only [encode, BrokenTradeOrderExecutedMessage.encode_length]
    omega
  | noiiMessage inner =>
    simp only [encode, NoiiMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UdpPayload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (OptionsDirectoryMessage.decode bytes).map fun (message, rest) => (.optionsDirectoryMessage message, rest)
  else if tag = 72 then (TradingActionMessage.decode bytes).map fun (message, rest) => (.tradingActionMessage message, rest)
  else if tag = 79 then (SecurityOpenMessage.decode bytes).map fun (message, rest) => (.securityOpenMessage message, rest)
  else if tag = 97 then (AddOrderMessageShortMessageForm.decode bytes).map fun (message, rest) => (.addOrderMessageShortMessageForm message, rest)
  else if tag = 65 then (AddOrderMessageLongFormMessage.decode bytes).map fun (message, rest) => (.addOrderMessageLongFormMessage message, rest)
  else if tag = 106 then (AddQuoteMessageShortFormMessage.decode bytes).map fun (message, rest) => (.addQuoteMessageShortFormMessage message, rest)
  else if tag = 74 then (AddQuoteMessageLongFormMessage.decode bytes).map fun (message, rest) => (.addQuoteMessageLongFormMessage message, rest)
  else if tag = 69 then (SingleSideExecutedMessage.decode bytes).map fun (message, rest) => (.singleSideExecutedMessage message, rest)
  else if tag = 67 then (SingleSideExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.singleSideExecutedWithPriceMessage message, rest)
  else if tag = 88 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 117 then (SingleSideReplaceMessageShortForm.decode bytes).map fun (message, rest) => (.singleSideReplaceMessageShortForm message, rest)
  else if tag = 85 then (SingleSideReplaceMessageLongForm.decode bytes).map fun (message, rest) => (.singleSideReplaceMessageLongForm message, rest)
  else if tag = 68 then (SingleSideDeleteMessage.decode bytes).map fun (message, rest) => (.singleSideDeleteMessage message, rest)
  else if tag = 71 then (SingleSideChangeMessage.decode bytes).map fun (message, rest) => (.singleSideChangeMessage message, rest)
  else if tag = 107 then (QuoteReplaceMessageShortForm.decode bytes).map fun (message, rest) => (.quoteReplaceMessageShortForm message, rest)
  else if tag = 75 then (QuoteReplaceMessageLongForm.decode bytes).map fun (message, rest) => (.quoteReplaceMessageLongForm message, rest)
  else if tag = 89 then (QuoteDeleteMessage.decode bytes).map fun (message, rest) => (.quoteDeleteMessage message, rest)
  else if tag = 80 then (OptionsTradeMessagesNonAuction.decode bytes).map fun (message, rest) => (.optionsTradeMessagesNonAuction message, rest)
  else if tag = 81 then (OptionsCrossTradeMessage.decode bytes).map fun (message, rest) => (.optionsCrossTradeMessage message, rest)
  else if tag = 66 then (BrokenTradeOrderExecutedMessage.decode bytes).map fun (message, rest) => (.brokenTradeOrderExecutedMessage message, rest)
  else if tag = 73 then (NoiiMessage.decode bytes).map fun (message, rest) => (.noiiMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UdpPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UdpPayload

/-- Message -/
structure Message where
  udpPayload : UdpPayload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (UdpPayload.tag message.udpPayload)
    ++ (UdpPayload.encode message.udpPayload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (udpPayload, bytes) ← UdpPayload.decode messageType bytes
  pure ({ udpPayload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UdpPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.udpPayload with
  | systemEventMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | optionsDirectoryMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, OptionsDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, TradingActionMessage.encode_length]
    omega
  | securityOpenMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, SecurityOpenMessage.encode_length]
    omega
  | addOrderMessageShortMessageForm inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, AddOrderMessageShortMessageForm.encode_length]
    omega
  | addOrderMessageLongFormMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, AddOrderMessageLongFormMessage.encode_length]
    omega
  | addQuoteMessageShortFormMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, AddQuoteMessageShortFormMessage.encode_length]
    omega
  | addQuoteMessageLongFormMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, AddQuoteMessageLongFormMessage.encode_length]
    omega
  | singleSideExecutedMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, SingleSideExecutedMessage.encode_length]
    omega
  | singleSideExecutedWithPriceMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, SingleSideExecutedWithPriceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, OrderCancelMessage.encode_length]
    omega
  | singleSideReplaceMessageShortForm inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, SingleSideReplaceMessageShortForm.encode_length]
    omega
  | singleSideReplaceMessageLongForm inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, SingleSideReplaceMessageLongForm.encode_length]
    omega
  | singleSideDeleteMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, SingleSideDeleteMessage.encode_length]
    omega
  | singleSideChangeMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, SingleSideChangeMessage.encode_length]
    omega
  | quoteReplaceMessageShortForm inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, QuoteReplaceMessageShortForm.encode_length]
    omega
  | quoteReplaceMessageLongForm inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, QuoteReplaceMessageLongForm.encode_length]
    omega
  | quoteDeleteMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, QuoteDeleteMessage.encode_length]
    omega
  | optionsTradeMessagesNonAuction inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, OptionsTradeMessagesNonAuction.encode_length]
    omega
  | optionsCrossTradeMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, OptionsCrossTradeMessage.encode_length]
    omega
  | brokenTradeOrderExecutedMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, BrokenTradeOrderExecutedMessage.encode_length]
    omega
  | noiiMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, NoiiMessage.encode_length]
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

/-- Mold Udp 64 Packet -/
structure MoldUdp64Packet where
  udpSession : Alpha 10
  udpSequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace MoldUdp64Packet

def encode (message : MoldUdp64Packet) : List UInt8 :=
  Alpha.encode message.udpSession
    ++ (encodeUInt 8 message.udpSequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (MoldUdp64Packet × List UInt8) := do
  let (udpSession, bytes) ← Alpha.decode 10 bytes
  let (udpSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ udpSession, udpSequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : MoldUdp64Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : MoldUdp64Packet) (rest : List UInt8) :
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

end MoldUdp64Packet

end Omi.NasdaqNomoptionsIttoItchV40MoldUdp64
