import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Depth Of Market v1.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqPhlxoptionsDepthofmarketItchV15

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
  [0x4E, 0x4C, 0x57]

inductive OptionsClosingType where
  | normal -- Normal
  | late -- Late
  | wcoEarlyClosing -- Wco Early Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionsClosingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionsClosingType

def toByte : OptionsClosingType → UInt8
  | .normal => 0x4E
  | .late => 0x4C
  | .wcoEarlyClosing => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionsClosingType :=
  if byte = 0x4E then .normal
  else if byte = 0x4C then .late
  else .wcoEarlyClosing

def ofByte (byte : UInt8) : OptionsClosingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionsClosingType) : ofByte value.toByte = value := by
  cases value with
  | normal => decide
  | late => decide
  | wcoEarlyClosing => decide
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
  [0x59, 0x4E]

inductive Tradable where
  | tradable -- Tradable
  | notTradable -- Not Tradable
  | unlisted (byte : { byte : UInt8 // byte ∉ Tradable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tradable

def toByte : Tradable → UInt8
  | .tradable => 0x59
  | .notTradable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tradable :=
  if byte = 0x59 then .tradable
  else .notTradable

def ofByte (byte : UInt8) : Tradable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tradable) : ofByte value.toByte = value := by
  cases value with
  | tradable => decide
  | notTradable => decide
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
  | buySideTradingSuspendedExhausted -- Buy Side Trading Suspended Exhausted
  | sellSideTradingSuspendedExhausted -- Sell Side Trading Suspended Exhausted
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .halt => 0x48
  | .trading => 0x54
  | .buySideTradingSuspendedExhausted => 0x42
  | .sellSideTradingSuspendedExhausted => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .halt
  else if byte = 0x54 then .trading
  else if byte = 0x42 then .buySideTradingSuspendedExhausted
  else .sellSideTradingSuspendedExhausted

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | halt => decide
  | trading => decide
  | buySideTradingSuspendedExhausted => decide
  | sellSideTradingSuspendedExhausted => decide
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
  [0x42, 0x53, 0x58, 0x59, 0x4D, 0x4E]

inductive MarketSide where
  | buy -- Buy
  | sell -- Sell
  | buyAon -- Buy Aon
  | sellAon -- Sell Aon
  | buyImplied -- Buy Implied
  | sellImplied -- Sell Implied
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketSide

def toByte : MarketSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .buyAon => 0x58
  | .sellAon => 0x59
  | .buyImplied => 0x4D
  | .sellImplied => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x58 then .buyAon
  else if byte = 0x59 then .sellAon
  else if byte = 0x4D then .buyImplied
  else .sellImplied

def ofByte (byte : UInt8) : MarketSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | buyAon => decide
  | sellAon => decide
  | buyImplied => decide
  | sellImplied => decide
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
  [0x55, 0x52, 0x53, 0x45]

inductive ChangeReason where
  | user -- User
  | reprice -- Reprice
  | suspend -- Suspend
  | exhausted -- Exhausted
  | unlisted (byte : { byte : UInt8 // byte ∉ ChangeReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ChangeReason

def toByte : ChangeReason → UInt8
  | .user => 0x55
  | .reprice => 0x52
  | .suspend => 0x53
  | .exhausted => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ChangeReason :=
  if byte = 0x55 then .user
  else if byte = 0x52 then .reprice
  else if byte = 0x53 then .suspend
  else .exhausted

def ofByte (byte : UInt8) : ChangeReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ChangeReason) : ofByte value.toByte = value := by
  cases value with
  | user => decide
  | reprice => decide
  | suspend => decide
  | exhausted => decide
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

/-- Trade Indicator: one byte code -/
def TradeIndicator.codes : List UInt8 :=
  [0x4F, 0x43, 0x50]

inductive TradeIndicator where
  | nonDisplayable -- Non Displayable
  | complex -- Complex
  | pixl -- Pixl
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeIndicator

def toByte : TradeIndicator → UInt8
  | .nonDisplayable => 0x4F
  | .complex => 0x43
  | .pixl => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeIndicator :=
  if byte = 0x4F then .nonDisplayable
  else if byte = 0x43 then .complex
  else .pixl

def ofByte (byte : UInt8) : TradeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeIndicator) : ofByte value.toByte = value := by
  cases value with
  | nonDisplayable => decide
  | complex => decide
  | pixl => decide
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

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x4F]

inductive CrossType where
  | openingReopening -- Opening Reopening
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .openingReopening => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : CrossType :=
  .openingReopening

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | openingReopening => decide
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
  [0x4F, 0x52, 0x49]

inductive AuctionType where
  | opening -- Opening
  | reopening -- Reopening
  | exposure -- Exposure
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .opening => 0x4F
  | .reopening => 0x52
  | .exposure => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x4F then .opening
  else if byte = 0x52 then .reopening
  else .exposure

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | opening => decide
  | reopening => decide
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

/-- Customer Indicator: one byte code -/
def CustomerIndicator.codes : List UInt8 :=
  [0x43, 0x46, 0x4D, 0x50, 0x42]

inductive CustomerIndicator where
  | customer -- Customer
  | firm -- Firm
  | onfloor -- Onfloor
  | professional -- Professional
  | nonPhlx -- Non Phlx
  | unlisted (byte : { byte : UInt8 // byte ∉ CustomerIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CustomerIndicator

def toByte : CustomerIndicator → UInt8
  | .customer => 0x43
  | .firm => 0x46
  | .onfloor => 0x4D
  | .professional => 0x50
  | .nonPhlx => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CustomerIndicator :=
  if byte = 0x43 then .customer
  else if byte = 0x46 then .firm
  else if byte = 0x4D then .onfloor
  else if byte = 0x50 then .professional
  else .nonPhlx

def ofByte (byte : UInt8) : CustomerIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CustomerIndicator) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | firm => decide
  | onfloor => decide
  | professional => decide
  | nonPhlx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CustomerIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CustomerIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CustomerIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CustomerIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CustomerIndicator

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
  eventCode : Alpha 1
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← Alpha.decode 1 bytes
  pure ({ nanoseconds, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
  let (tradable_, bytes) ← Tradable.decode bytes
  let (mpv, bytes) ← Mpv.decode bytes
  pure ({ nanoseconds, optionId, securitySymbol, expirationYear, expirationMonth, expirationDate, explicitStrikePrice, optionType, source, underlyingSymbol, optionsClosingType, tradable := tradable_, mpv }, bytes)

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

/-- Security Open Message: 9 bytes -/
structure SecurityOpenMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  openState : OpenState
  deriving DecidableEq, Repr

namespace SecurityOpenMessage

def encode (message : SecurityOpenMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (OpenState.encode message.openState))

def decode (bytes : List UInt8) : Option (SecurityOpenMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (openState, bytes) ← OpenState.decode bytes
  pure ({ nanoseconds, optionId, openState }, bytes)

@[simp] theorem encode_length (message : SecurityOpenMessage) : (encode message).length = 9 := by
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
  rw [OpenState.decode_encode, some_bind]
  rfl

end SecurityOpenMessage

/-- Add Order Message Short Form: 21 bytes -/
structure AddOrderMessageShortForm where
  nanoseconds : BitVec 32
  orderReferenceNumberDelta : BitVec 32
  marketSide : MarketSide
  optionId : BitVec 32
  shortPrice : BitVec 16
  shortVolume : BitVec 16
  orderId : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessageShortForm

def encode (message : AddOrderMessageShortForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderReferenceNumberDelta
    ++ (MarketSide.encode message.marketSide
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 2 message.shortPrice
    ++ (encodeUInt 2 message.shortVolume
    ++ (encodeUInt 4 message.orderId))))))

def decode (bytes : List UInt8) : Option (AddOrderMessageShortForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (marketSide, bytes) ← MarketSide.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (shortPrice, bytes) ← decodeUInt 2 bytes
  let (shortVolume, bytes) ← decodeUInt 2 bytes
  let (orderId, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderReferenceNumberDelta, marketSide, optionId, shortPrice, shortVolume, orderId }, bytes)

@[simp] theorem encode_length (message : AddOrderMessageShortForm) : (encode message).length = 21 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessageShortForm

/-- Add Order Message Long Form: 25 bytes -/
structure AddOrderMessageLongForm where
  nanoseconds : BitVec 32
  orderReferenceNumberDelta : BitVec 32
  marketSide : MarketSide
  optionId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  orderId : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessageLongForm

def encode (message : AddOrderMessageLongForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderReferenceNumberDelta
    ++ (MarketSide.encode message.marketSide
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.orderId))))))

def decode (bytes : List UInt8) : Option (AddOrderMessageLongForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (marketSide, bytes) ← MarketSide.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderReferenceNumberDelta, marketSide, optionId, price, volume, orderId }, bytes)

@[simp] theorem encode_length (message : AddOrderMessageLongForm) : (encode message).length = 25 := by
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
  shortBidSize : BitVec 16
  askPrice : BitVec 16
  shortAskSize : BitVec 16
  deriving DecidableEq, Repr

namespace AddQuoteMessageShortForm

def encode (message : AddQuoteMessageShortForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.bidReferenceNumberDelta
    ++ (encodeUInt 4 message.askReferenceNumberDelta
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 2 message.bidPrice
    ++ (encodeUInt 2 message.shortBidSize
    ++ (encodeUInt 2 message.askPrice
    ++ (encodeUInt 2 message.shortAskSize)))))))

def decode (bytes : List UInt8) : Option (AddQuoteMessageShortForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (askReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (bidPrice, bytes) ← decodeUInt 2 bytes
  let (shortBidSize, bytes) ← decodeUInt 2 bytes
  let (askPrice, bytes) ← decodeUInt 2 bytes
  let (shortAskSize, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, bidReferenceNumberDelta, askReferenceNumberDelta, optionId, bidPrice, shortBidSize, askPrice, shortAskSize }, bytes)

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
  bidSize : BitVec 32
  ask : BitVec 32
  askSize : BitVec 32
  deriving DecidableEq, Repr

namespace AddQuoteMessageLongForm

def encode (message : AddQuoteMessageLongForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.bidReferenceNumberDelta
    ++ (encodeUInt 4 message.askReferenceNumberDelta
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.bid
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 4 message.ask
    ++ (encodeUInt 4 message.askSize)))))))

def decode (bytes : List UInt8) : Option (AddQuoteMessageLongForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (askReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (bid, bytes) ← decodeUInt 4 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (ask, bytes) ← decodeUInt 4 bytes
  let (askSize, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, bidReferenceNumberDelta, askReferenceNumberDelta, optionId, bid, bidSize, ask, askSize }, bytes)

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

/-- Single Side Executed With Price Message: 25 bytes -/
structure SingleSideExecutedWithPriceMessage where
  nanoseconds : BitVec 32
  referenceNumberDelta : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  printable : Printable
  price : BitVec 32
  volume : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideExecutedWithPriceMessage

def encode (message : SingleSideExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.referenceNumberDelta
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber
    ++ (Printable.encode message.printable
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume))))))

def decode (bytes : List UInt8) : Option (SingleSideExecutedWithPriceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (referenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, referenceNumberDelta, crossNumber, matchNumber, printable := printable_, price, volume }, bytes)

@[simp] theorem encode_length (message : SingleSideExecutedWithPriceMessage) : (encode message).length = 25 := by
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
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleSideExecutedWithPriceMessage

/-- Single Side Cancel Message: 12 bytes -/
structure SingleSideCancelMessage where
  nanoseconds : BitVec 32
  referenceNumberDelta : BitVec 32
  cancelledContracts : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideCancelMessage

def encode (message : SingleSideCancelMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.referenceNumberDelta
    ++ (encodeUInt 4 message.cancelledContracts))

def decode (bytes : List UInt8) : Option (SingleSideCancelMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (referenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (cancelledContracts, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, referenceNumberDelta, cancelledContracts }, bytes)

@[simp] theorem encode_length (message : SingleSideCancelMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SingleSideCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleSideCancelMessage

/-- Single Side Replace Message Short Form: 16 bytes -/
structure SingleSideReplaceMessageShortForm where
  nanoseconds : BitVec 32
  originalReferenceNumberDelta : BitVec 32
  newReferenceNumberDelta : BitVec 32
  shortPrice : BitVec 16
  shortVolume : BitVec 16
  deriving DecidableEq, Repr

namespace SingleSideReplaceMessageShortForm

def encode (message : SingleSideReplaceMessageShortForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.originalReferenceNumberDelta
    ++ (encodeUInt 4 message.newReferenceNumberDelta
    ++ (encodeUInt 2 message.shortPrice
    ++ (encodeUInt 2 message.shortVolume))))

def decode (bytes : List UInt8) : Option (SingleSideReplaceMessageShortForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (originalReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (newReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (shortPrice, bytes) ← decodeUInt 2 bytes
  let (shortVolume, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, originalReferenceNumberDelta, newReferenceNumberDelta, shortPrice, shortVolume }, bytes)

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
  price : BitVec 32
  volume : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideReplaceMessageLongForm

def encode (message : SingleSideReplaceMessageLongForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.originalReferenceNumberDelta
    ++ (encodeUInt 4 message.newReferenceNumberDelta
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume))))

def decode (bytes : List UInt8) : Option (SingleSideReplaceMessageLongForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (originalReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (newReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, originalReferenceNumberDelta, newReferenceNumberDelta, price, volume }, bytes)

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

/-- Order Replace Message Short Form: 20 bytes -/
structure OrderReplaceMessageShortForm where
  nanoseconds : BitVec 32
  originalReferenceNumberDelta : BitVec 32
  newReferenceNumberDelta : BitVec 32
  shortPrice : BitVec 16
  shortVolume : BitVec 16
  orderId : BitVec 32
  deriving DecidableEq, Repr

namespace OrderReplaceMessageShortForm

def encode (message : OrderReplaceMessageShortForm) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.originalReferenceNumberDelta
    ++ (encodeUInt 4 message.newReferenceNumberDelta
    ++ (encodeUInt 2 message.shortPrice
    ++ (encodeUInt 2 message.shortVolume
    ++ (encodeUInt 4 message.orderId)))))

def decode (bytes : List UInt8) : Option (OrderReplaceMessageShortForm × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (originalReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (newReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (shortPrice, bytes) ← decodeUInt 2 bytes
  let (shortVolume, bytes) ← decodeUInt 2 bytes
  let (orderId, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, originalReferenceNumberDelta, newReferenceNumberDelta, shortPrice, shortVolume, orderId }, bytes)

@[simp] theorem encode_length (message : OrderReplaceMessageShortForm) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderReplaceMessageShortForm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceMessageShortForm) (rest : List UInt8) :
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

end OrderReplaceMessageShortForm

/-- Single Side Replace Long Form Message: 24 bytes -/
structure SingleSideReplaceLongFormMessage where
  nanoseconds : BitVec 32
  originalReferenceNumberDelta : BitVec 32
  newReferenceNumberDelta : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  orderId : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideReplaceLongFormMessage

def encode (message : SingleSideReplaceLongFormMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.originalReferenceNumberDelta
    ++ (encodeUInt 4 message.newReferenceNumberDelta
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.orderId)))))

def decode (bytes : List UInt8) : Option (SingleSideReplaceLongFormMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (originalReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (newReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, originalReferenceNumberDelta, newReferenceNumberDelta, price, volume, orderId }, bytes)

@[simp] theorem encode_length (message : SingleSideReplaceLongFormMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SingleSideReplaceLongFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideReplaceLongFormMessage) (rest : List UInt8) :
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

end SingleSideReplaceLongFormMessage

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
  price : BitVec 32
  volume : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideUpdateMessage

def encode (message : SingleSideUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.referenceNumberDelta
    ++ (ChangeReason.encode message.changeReason
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume))))

def decode (bytes : List UInt8) : Option (SingleSideUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (referenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (changeReason, bytes) ← ChangeReason.decode bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, referenceNumberDelta, changeReason, price, volume }, bytes)

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

/-- Quote Replace Short Form Message: 28 bytes -/
structure QuoteReplaceShortFormMessage where
  nanoseconds : BitVec 32
  originalBidReferenceNumberDelta : BitVec 32
  bidReferenceNumberDelta : BitVec 32
  originalAskReferenceNumberDelta : BitVec 32
  askReferenceNumberDelta : BitVec 32
  bidPrice : BitVec 16
  shortBidSize : BitVec 16
  askPrice : BitVec 16
  shortAskSize : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteReplaceShortFormMessage

def encode (message : QuoteReplaceShortFormMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.originalBidReferenceNumberDelta
    ++ (encodeUInt 4 message.bidReferenceNumberDelta
    ++ (encodeUInt 4 message.originalAskReferenceNumberDelta
    ++ (encodeUInt 4 message.askReferenceNumberDelta
    ++ (encodeUInt 2 message.bidPrice
    ++ (encodeUInt 2 message.shortBidSize
    ++ (encodeUInt 2 message.askPrice
    ++ (encodeUInt 2 message.shortAskSize))))))))

def decode (bytes : List UInt8) : Option (QuoteReplaceShortFormMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (originalBidReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (originalAskReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (askReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (bidPrice, bytes) ← decodeUInt 2 bytes
  let (shortBidSize, bytes) ← decodeUInt 2 bytes
  let (askPrice, bytes) ← decodeUInt 2 bytes
  let (shortAskSize, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, originalBidReferenceNumberDelta, bidReferenceNumberDelta, originalAskReferenceNumberDelta, askReferenceNumberDelta, bidPrice, shortBidSize, askPrice, shortAskSize }, bytes)

@[simp] theorem encode_length (message : QuoteReplaceShortFormMessage) : (encode message).length = 28 := by
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuoteReplaceShortFormMessage

/-- Quote Replace Long Form Message: 36 bytes -/
structure QuoteReplaceLongFormMessage where
  nanoseconds : BitVec 32
  originalBidReferenceNumberDelta : BitVec 32
  bidReferenceNumberDelta : BitVec 32
  originalAskReferenceNumberDelta : BitVec 32
  askReferenceNumberDelta : BitVec 32
  bid : BitVec 32
  bidSize : BitVec 32
  ask : BitVec 32
  askSize : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteReplaceLongFormMessage

def encode (message : QuoteReplaceLongFormMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.originalBidReferenceNumberDelta
    ++ (encodeUInt 4 message.bidReferenceNumberDelta
    ++ (encodeUInt 4 message.originalAskReferenceNumberDelta
    ++ (encodeUInt 4 message.askReferenceNumberDelta
    ++ (encodeUInt 4 message.bid
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 4 message.ask
    ++ (encodeUInt 4 message.askSize))))))))

def decode (bytes : List UInt8) : Option (QuoteReplaceLongFormMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (originalBidReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (originalAskReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (askReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  let (bid, bytes) ← decodeUInt 4 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (ask, bytes) ← decodeUInt 4 bytes
  let (askSize, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, originalBidReferenceNumberDelta, bidReferenceNumberDelta, originalAskReferenceNumberDelta, askReferenceNumberDelta, bid, bidSize, ask, askSize }, bytes)

@[simp] theorem encode_length (message : QuoteReplaceLongFormMessage) : (encode message).length = 36 := by
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuoteReplaceLongFormMessage

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
  numberOfReferenceNumberDeltas : BitVec 16
  cancelledReferenceNumberDelta : BitVec 32
  deriving DecidableEq, Repr

namespace BlockDeleteMessage

def encode (message : BlockDeleteMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.numberOfReferenceNumberDeltas
    ++ (encodeUInt 4 message.cancelledReferenceNumberDelta))

def decode (bytes : List UInt8) : Option (BlockDeleteMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (numberOfReferenceNumberDeltas, bytes) ← decodeUInt 2 bytes
  let (cancelledReferenceNumberDelta, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, numberOfReferenceNumberDeltas, cancelledReferenceNumberDelta }, bytes)

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
  tradeIndicator : TradeIndicator
  optionId : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  deriving DecidableEq, Repr

namespace NonAuctionOptionsTradeMessage

def encode (message : NonAuctionOptionsTradeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (TradeIndicator.encode message.tradeIndicator
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume))))))

def decode (bytes : List UInt8) : Option (NonAuctionOptionsTradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeIndicator, bytes) ← TradeIndicator.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeIndicator, optionId, crossNumber, matchNumber, price, volume }, bytes)

@[simp] theorem encode_length (message : NonAuctionOptionsTradeMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradeIndicator.encode_length]

theorem encode_length_pos (message : NonAuctionOptionsTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NonAuctionOptionsTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeIndicator.decode_encode, some_bind]
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
  price : BitVec 32
  volume : BitVec 32
  deriving DecidableEq, Repr

namespace OptionsCrossTradeMessage

def encode (message : OptionsCrossTradeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber
    ++ (CrossType.encode message.crossType
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume))))))

def decode (bytes : List UInt8) : Option (OptionsCrossTradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, optionId, crossNumber, matchNumber, crossType, price, volume }, bytes)

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

/-- Broken Trade Order Execution Message: 12 bytes -/
structure BrokenTradeOrderExecutionMessage where
  nanoseconds : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  deriving DecidableEq, Repr

namespace BrokenTradeOrderExecutionMessage

def encode (message : BrokenTradeOrderExecutionMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber))

def decode (bytes : List UInt8) : Option (BrokenTradeOrderExecutionMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, crossNumber, matchNumber }, bytes)

@[simp] theorem encode_length (message : BrokenTradeOrderExecutionMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BrokenTradeOrderExecutionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeOrderExecutionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BrokenTradeOrderExecutionMessage

/-- Auction Notification Message: 30 bytes -/
structure AuctionNotificationMessage where
  nanoseconds : BitVec 32
  auctionId : BitVec 32
  auctionType : AuctionType
  pairedContracts : BitVec 32
  imbalanceDirection : ImbalanceDirection
  optionId : BitVec 32
  imbalancePrice : BitVec 32
  imbalanceVolume : BitVec 32
  customerIndicator : CustomerIndicator
  reserved3 : BitVec 24
  deriving DecidableEq, Repr

namespace AuctionNotificationMessage

def encode (message : AuctionNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.auctionId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.pairedContracts
    ++ (ImbalanceDirection.encode message.imbalanceDirection
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.imbalancePrice
    ++ (encodeUInt 4 message.imbalanceVolume
    ++ (CustomerIndicator.encode message.customerIndicator
    ++ (encodeUInt 3 message.reserved3)))))))))

def decode (bytes : List UInt8) : Option (AuctionNotificationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (pairedContracts, bytes) ← decodeUInt 4 bytes
  let (imbalanceDirection, bytes) ← ImbalanceDirection.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (imbalancePrice, bytes) ← decodeUInt 4 bytes
  let (imbalanceVolume, bytes) ← decodeUInt 4 bytes
  let (customerIndicator, bytes) ← CustomerIndicator.decode bytes
  let (reserved3, bytes) ← decodeUInt 3 bytes
  pure ({ nanoseconds, auctionId, auctionType, pairedContracts, imbalanceDirection, optionId, imbalancePrice, imbalanceVolume, customerIndicator, reserved3 }, bytes)

@[simp] theorem encode_length (message : AuctionNotificationMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, AuctionType.encode_length, ImbalanceDirection.encode_length, CustomerIndicator.encode_length]

theorem encode_length_pos (message : AuctionNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CustomerIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AuctionNotificationMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | secondsMessage (message : SecondsMessage) -- "T" 0x54
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | baseReferenceMessage (message : BaseReferenceMessage) -- "L" 0x4C
  | optionDirectoryMessage (message : OptionDirectoryMessage) -- "R" 0x52
  | tradingActionMessage (message : TradingActionMessage) -- "H" 0x48
  | securityOpenMessage (message : SecurityOpenMessage) -- "O" 0x4F
  | addOrderMessageShortForm (message : AddOrderMessageShortForm) -- "a" 0x61
  | addOrderMessageLongForm (message : AddOrderMessageLongForm) -- "A" 0x41
  | addQuoteMessageShortForm (message : AddQuoteMessageShortForm) -- "j" 0x6A
  | addQuoteMessageLongForm (message : AddQuoteMessageLongForm) -- "J" 0x4A
  | singleSideExecutedMessage (message : SingleSideExecutedMessage) -- "E" 0x45
  | singleSideExecutedWithPriceMessage (message : SingleSideExecutedWithPriceMessage) -- "C" 0x43
  | singleSideCancelMessage (message : SingleSideCancelMessage) -- "X" 0x58
  | singleSideReplaceMessageShortForm (message : SingleSideReplaceMessageShortForm) -- "u" 0x75
  | singleSideReplaceMessageLongForm (message : SingleSideReplaceMessageLongForm) -- "U" 0x55
  | orderReplaceMessageShortForm (message : OrderReplaceMessageShortForm) -- "v" 0x76
  | singleSideReplaceLongFormMessage (message : SingleSideReplaceLongFormMessage) -- "V" 0x56
  | singleSideDeleteMessage (message : SingleSideDeleteMessage) -- "D" 0x44
  | singleSideUpdateMessage (message : SingleSideUpdateMessage) -- "G" 0x47
  | quoteReplaceShortFormMessage (message : QuoteReplaceShortFormMessage) -- "k" 0x6B
  | quoteReplaceLongFormMessage (message : QuoteReplaceLongFormMessage) -- "K" 0x4B
  | quoteDeleteMessage (message : QuoteDeleteMessage) -- "Y" 0x59
  | blockDeleteMessage (message : BlockDeleteMessage) -- "Z" 0x5A
  | nonAuctionOptionsTradeMessage (message : NonAuctionOptionsTradeMessage) -- "P" 0x50
  | optionsCrossTradeMessage (message : OptionsCrossTradeMessage) -- "Q" 0x51
  | brokenTradeOrderExecutionMessage (message : BrokenTradeOrderExecutionMessage) -- "B" 0x42
  | auctionNotificationMessage (message : AuctionNotificationMessage) -- "I" 0x49
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .secondsMessage _ => 84
  | .systemEventMessage _ => 83
  | .baseReferenceMessage _ => 76
  | .optionDirectoryMessage _ => 82
  | .tradingActionMessage _ => 72
  | .securityOpenMessage _ => 79
  | .addOrderMessageShortForm _ => 97
  | .addOrderMessageLongForm _ => 65
  | .addQuoteMessageShortForm _ => 106
  | .addQuoteMessageLongForm _ => 74
  | .singleSideExecutedMessage _ => 69
  | .singleSideExecutedWithPriceMessage _ => 67
  | .singleSideCancelMessage _ => 88
  | .singleSideReplaceMessageShortForm _ => 117
  | .singleSideReplaceMessageLongForm _ => 85
  | .orderReplaceMessageShortForm _ => 118
  | .singleSideReplaceLongFormMessage _ => 86
  | .singleSideDeleteMessage _ => 68
  | .singleSideUpdateMessage _ => 71
  | .quoteReplaceShortFormMessage _ => 107
  | .quoteReplaceLongFormMessage _ => 75
  | .quoteDeleteMessage _ => 89
  | .blockDeleteMessage _ => 90
  | .nonAuctionOptionsTradeMessage _ => 80
  | .optionsCrossTradeMessage _ => 81
  | .brokenTradeOrderExecutionMessage _ => 66
  | .auctionNotificationMessage _ => 73

def encode : Payload → List UInt8
  | .secondsMessage message => SecondsMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .baseReferenceMessage message => BaseReferenceMessage.encode message
  | .optionDirectoryMessage message => OptionDirectoryMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .securityOpenMessage message => SecurityOpenMessage.encode message
  | .addOrderMessageShortForm message => AddOrderMessageShortForm.encode message
  | .addOrderMessageLongForm message => AddOrderMessageLongForm.encode message
  | .addQuoteMessageShortForm message => AddQuoteMessageShortForm.encode message
  | .addQuoteMessageLongForm message => AddQuoteMessageLongForm.encode message
  | .singleSideExecutedMessage message => SingleSideExecutedMessage.encode message
  | .singleSideExecutedWithPriceMessage message => SingleSideExecutedWithPriceMessage.encode message
  | .singleSideCancelMessage message => SingleSideCancelMessage.encode message
  | .singleSideReplaceMessageShortForm message => SingleSideReplaceMessageShortForm.encode message
  | .singleSideReplaceMessageLongForm message => SingleSideReplaceMessageLongForm.encode message
  | .orderReplaceMessageShortForm message => OrderReplaceMessageShortForm.encode message
  | .singleSideReplaceLongFormMessage message => SingleSideReplaceLongFormMessage.encode message
  | .singleSideDeleteMessage message => SingleSideDeleteMessage.encode message
  | .singleSideUpdateMessage message => SingleSideUpdateMessage.encode message
  | .quoteReplaceShortFormMessage message => QuoteReplaceShortFormMessage.encode message
  | .quoteReplaceLongFormMessage message => QuoteReplaceLongFormMessage.encode message
  | .quoteDeleteMessage message => QuoteDeleteMessage.encode message
  | .blockDeleteMessage message => BlockDeleteMessage.encode message
  | .nonAuctionOptionsTradeMessage message => NonAuctionOptionsTradeMessage.encode message
  | .optionsCrossTradeMessage message => OptionsCrossTradeMessage.encode message
  | .brokenTradeOrderExecutionMessage message => BrokenTradeOrderExecutionMessage.encode message
  | .auctionNotificationMessage message => AuctionNotificationMessage.encode message

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
  | securityOpenMessage inner =>
    simp only [encode, SecurityOpenMessage.encode_length]
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
  | singleSideExecutedWithPriceMessage inner =>
    simp only [encode, SingleSideExecutedWithPriceMessage.encode_length]
    omega
  | singleSideCancelMessage inner =>
    simp only [encode, SingleSideCancelMessage.encode_length]
    omega
  | singleSideReplaceMessageShortForm inner =>
    simp only [encode, SingleSideReplaceMessageShortForm.encode_length]
    omega
  | singleSideReplaceMessageLongForm inner =>
    simp only [encode, SingleSideReplaceMessageLongForm.encode_length]
    omega
  | orderReplaceMessageShortForm inner =>
    simp only [encode, OrderReplaceMessageShortForm.encode_length]
    omega
  | singleSideReplaceLongFormMessage inner =>
    simp only [encode, SingleSideReplaceLongFormMessage.encode_length]
    omega
  | singleSideDeleteMessage inner =>
    simp only [encode, SingleSideDeleteMessage.encode_length]
    omega
  | singleSideUpdateMessage inner =>
    simp only [encode, SingleSideUpdateMessage.encode_length]
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
  | blockDeleteMessage inner =>
    simp only [encode, BlockDeleteMessage.encode_length]
    omega
  | nonAuctionOptionsTradeMessage inner =>
    simp only [encode, NonAuctionOptionsTradeMessage.encode_length]
    omega
  | optionsCrossTradeMessage inner =>
    simp only [encode, OptionsCrossTradeMessage.encode_length]
    omega
  | brokenTradeOrderExecutionMessage inner =>
    simp only [encode, BrokenTradeOrderExecutionMessage.encode_length]
    omega
  | auctionNotificationMessage inner =>
    simp only [encode, AuctionNotificationMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (SecondsMessage.decode bytes).map fun (message, rest) => (.secondsMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 76 then (BaseReferenceMessage.decode bytes).map fun (message, rest) => (.baseReferenceMessage message, rest)
  else if tag = 82 then (OptionDirectoryMessage.decode bytes).map fun (message, rest) => (.optionDirectoryMessage message, rest)
  else if tag = 72 then (TradingActionMessage.decode bytes).map fun (message, rest) => (.tradingActionMessage message, rest)
  else if tag = 79 then (SecurityOpenMessage.decode bytes).map fun (message, rest) => (.securityOpenMessage message, rest)
  else if tag = 97 then (AddOrderMessageShortForm.decode bytes).map fun (message, rest) => (.addOrderMessageShortForm message, rest)
  else if tag = 65 then (AddOrderMessageLongForm.decode bytes).map fun (message, rest) => (.addOrderMessageLongForm message, rest)
  else if tag = 106 then (AddQuoteMessageShortForm.decode bytes).map fun (message, rest) => (.addQuoteMessageShortForm message, rest)
  else if tag = 74 then (AddQuoteMessageLongForm.decode bytes).map fun (message, rest) => (.addQuoteMessageLongForm message, rest)
  else if tag = 69 then (SingleSideExecutedMessage.decode bytes).map fun (message, rest) => (.singleSideExecutedMessage message, rest)
  else if tag = 67 then (SingleSideExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.singleSideExecutedWithPriceMessage message, rest)
  else if tag = 88 then (SingleSideCancelMessage.decode bytes).map fun (message, rest) => (.singleSideCancelMessage message, rest)
  else if tag = 117 then (SingleSideReplaceMessageShortForm.decode bytes).map fun (message, rest) => (.singleSideReplaceMessageShortForm message, rest)
  else if tag = 85 then (SingleSideReplaceMessageLongForm.decode bytes).map fun (message, rest) => (.singleSideReplaceMessageLongForm message, rest)
  else if tag = 118 then (OrderReplaceMessageShortForm.decode bytes).map fun (message, rest) => (.orderReplaceMessageShortForm message, rest)
  else if tag = 86 then (SingleSideReplaceLongFormMessage.decode bytes).map fun (message, rest) => (.singleSideReplaceLongFormMessage message, rest)
  else if tag = 68 then (SingleSideDeleteMessage.decode bytes).map fun (message, rest) => (.singleSideDeleteMessage message, rest)
  else if tag = 71 then (SingleSideUpdateMessage.decode bytes).map fun (message, rest) => (.singleSideUpdateMessage message, rest)
  else if tag = 107 then (QuoteReplaceShortFormMessage.decode bytes).map fun (message, rest) => (.quoteReplaceShortFormMessage message, rest)
  else if tag = 75 then (QuoteReplaceLongFormMessage.decode bytes).map fun (message, rest) => (.quoteReplaceLongFormMessage message, rest)
  else if tag = 89 then (QuoteDeleteMessage.decode bytes).map fun (message, rest) => (.quoteDeleteMessage message, rest)
  else if tag = 90 then (BlockDeleteMessage.decode bytes).map fun (message, rest) => (.blockDeleteMessage message, rest)
  else if tag = 80 then (NonAuctionOptionsTradeMessage.decode bytes).map fun (message, rest) => (.nonAuctionOptionsTradeMessage message, rest)
  else if tag = 81 then (OptionsCrossTradeMessage.decode bytes).map fun (message, rest) => (.optionsCrossTradeMessage message, rest)
  else if tag = 66 then (BrokenTradeOrderExecutionMessage.decode bytes).map fun (message, rest) => (.brokenTradeOrderExecutionMessage message, rest)
  else if tag = 73 then (AuctionNotificationMessage.decode bytes).map fun (message, rest) => (.auctionNotificationMessage message, rest)
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
  | securityOpenMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityOpenMessage.encode_length]
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
  | singleSideExecutedWithPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SingleSideExecutedWithPriceMessage.encode_length]
    omega
  | singleSideCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SingleSideCancelMessage.encode_length]
    omega
  | singleSideReplaceMessageShortForm inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SingleSideReplaceMessageShortForm.encode_length]
    omega
  | singleSideReplaceMessageLongForm inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SingleSideReplaceMessageLongForm.encode_length]
    omega
  | orderReplaceMessageShortForm inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderReplaceMessageShortForm.encode_length]
    omega
  | singleSideReplaceLongFormMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SingleSideReplaceLongFormMessage.encode_length]
    omega
  | singleSideDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SingleSideDeleteMessage.encode_length]
    omega
  | singleSideUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SingleSideUpdateMessage.encode_length]
    omega
  | quoteReplaceShortFormMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteReplaceShortFormMessage.encode_length]
    omega
  | quoteReplaceLongFormMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteReplaceLongFormMessage.encode_length]
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
  | brokenTradeOrderExecutionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BrokenTradeOrderExecutionMessage.encode_length]
    omega
  | auctionNotificationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AuctionNotificationMessage.encode_length]
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

end Omi.NasdaqPhlxoptionsDepthofmarketItchV15
