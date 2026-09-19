import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Ise Order Feed Market Data v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqIseoptionsOrderfeedItchV11

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4E, 0x4C, 0x45, 0x43, 0x57]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfOpeningProcess -- Start Of Opening Process
  | startOfNormalHoursClosingProcess -- Start Of Normal Hours Closing Process
  | startOfLateHoursClosingProcess -- Start Of Late Hours Closing Process
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | endOfWcoEarlyClosing -- End Of Wco Early Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfOpeningProcess => 0x51
  | .startOfNormalHoursClosingProcess => 0x4E
  | .startOfLateHoursClosingProcess => 0x4C
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .endOfWcoEarlyClosing => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfOpeningProcess
  else if byte = 0x4E then .startOfNormalHoursClosingProcess
  else if byte = 0x4C then .startOfLateHoursClosingProcess
  else if byte = 0x45 then .endOfSystemHours
  else if byte = 0x43 then .endOfMessages
  else .endOfWcoEarlyClosing

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfOpeningProcess => decide
  | startOfNormalHoursClosingProcess => decide
  | startOfLateHoursClosingProcess => decide
  | endOfSystemHours => decide
  | endOfMessages => decide
  | endOfWcoEarlyClosing => decide
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

/-- Trading Type: one byte code -/
def TradingType.codes : List UInt8 :=
  [0x45, 0x49, 0x46, 0x43]

inductive TradingType where
  | equity -- Equity
  | index -- Index
  | etf -- Etf
  | currency -- Currency
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingType

def toByte : TradingType → UInt8
  | .equity => 0x45
  | .index => 0x49
  | .etf => 0x46
  | .currency => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingType :=
  if byte = 0x45 then .equity
  else if byte = 0x49 then .index
  else if byte = 0x46 then .etf
  else .currency

def ofByte (byte : UInt8) : TradingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingType) : ofByte value.toByte = value := by
  cases value with
  | equity => decide
  | index => decide
  | etf => decide
  | currency => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingType

/-- Option Closing Type: one byte code -/
def OptionClosingType.codes : List UInt8 :=
  [0x4E, 0x4C]

inductive OptionClosingType where
  | normal -- Normal
  | late -- Late
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionClosingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionClosingType

def toByte : OptionClosingType → UInt8
  | .normal => 0x4E
  | .late => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionClosingType :=
  if byte = 0x4E then .normal
  else .late

def ofByte (byte : UInt8) : OptionClosingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionClosingType) : ofByte value.toByte = value := by
  cases value with
  | normal => decide
  | late => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionClosingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionClosingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionClosingType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionClosingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionClosingType

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

/-- Closing Only: one byte code -/
def ClosingOnly.codes : List UInt8 :=
  [0x59, 0x4E]

inductive ClosingOnly where
  | closingPositionOnly -- Closing Position Only
  | notClosingPositionOnly -- Not Closing Position Only
  | unlisted (byte : { byte : UInt8 // byte ∉ ClosingOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClosingOnly

def toByte : ClosingOnly → UInt8
  | .closingPositionOnly => 0x59
  | .notClosingPositionOnly => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClosingOnly :=
  if byte = 0x59 then .closingPositionOnly
  else .notClosingPositionOnly

def ofByte (byte : UInt8) : ClosingOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClosingOnly) : ofByte value.toByte = value := by
  cases value with
  | closingPositionOnly => decide
  | notClosingPositionOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClosingOnly) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClosingOnly × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClosingOnly) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ClosingOnly) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClosingOnly

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x48, 0x54]

inductive CurrentTradingState where
  | haltInEffect -- Halt In Effect
  | tradingOnTheOptionsSystem -- Trading On The Options System
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .haltInEffect => 0x48
  | .tradingOnTheOptionsSystem => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .haltInEffect
  else .tradingOnTheOptionsSystem

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | haltInEffect => decide
  | tradingOnTheOptionsSystem => decide
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
  | openForAutoExecution -- Open For Auto Execution
  | closedForAutoExecution -- Closed For Auto Execution
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenState

def toByte : OpenState → UInt8
  | .openForAutoExecution => 0x59
  | .closedForAutoExecution => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenState :=
  if byte = 0x59 then .openForAutoExecution
  else .closedForAutoExecution

def ofByte (byte : UInt8) : OpenState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenState) : ofByte value.toByte = value := by
  cases value with
  | openForAutoExecution => decide
  | closedForAutoExecution => decide
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

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x4D, 0x4C]

inductive OrderType where
  | market -- Market
  | limit -- Limit
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .market => 0x4D
  | .limit => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x4D then .market
  else .limit

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | limit => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderType

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x41, 0x20]

inductive Side where
  | bid -- Bid
  | offerAsk -- Offer Ask
  | hidden -- Hidden
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .bid => 0x42
  | .offerAsk => 0x41
  | .hidden => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .bid
  else if byte = 0x41 then .offerAsk
  else .hidden

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | offerAsk => decide
  | hidden => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Exec Flag: one byte code -/
def ExecFlag.codes : List UInt8 :=
  [0x4E, 0x41, 0x20]

inductive ExecFlag where
  | none_ -- None
  | aon -- Aon
  | hidden -- Hidden
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecFlag

def toByte : ExecFlag → UInt8
  | .none_ => 0x4E
  | .aon => 0x41
  | .hidden => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecFlag :=
  if byte = 0x4E then .none_
  else if byte = 0x41 then .aon
  else .hidden

def ofByte (byte : UInt8) : ExecFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecFlag) : ofByte value.toByte = value := by
  cases value with
  | none_ => decide
  | aon => decide
  | hidden => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExecFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecFlag

/-- Order Capacity: one byte code -/
def OrderCapacity.codes : List UInt8 :=
  [0x43, 0x44, 0x46, 0x42, 0x4B, 0x45, 0x4E, 0x4D]

inductive OrderCapacity where
  | customer -- Customer
  | customerProfessional -- Customer Professional
  | firm -- Firm
  | brokerDealerCustomer -- Broker Dealer Customer
  | brokerDealerFirm -- Broker Dealer Firm
  | proprietary -- Proprietary
  | awayMarketMaker -- Away Market Maker
  | marketMaker -- Market Maker
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderCapacity

def toByte : OrderCapacity → UInt8
  | .customer => 0x43
  | .customerProfessional => 0x44
  | .firm => 0x46
  | .brokerDealerCustomer => 0x42
  | .brokerDealerFirm => 0x4B
  | .proprietary => 0x45
  | .awayMarketMaker => 0x4E
  | .marketMaker => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderCapacity :=
  if byte = 0x43 then .customer
  else if byte = 0x44 then .customerProfessional
  else if byte = 0x46 then .firm
  else if byte = 0x42 then .brokerDealerCustomer
  else if byte = 0x4B then .brokerDealerFirm
  else if byte = 0x45 then .proprietary
  else if byte = 0x4E then .awayMarketMaker
  else .marketMaker

def ofByte (byte : UInt8) : OrderCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderCapacity) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | customerProfessional => decide
  | firm => decide
  | brokerDealerCustomer => decide
  | brokerDealerFirm => decide
  | proprietary => decide
  | awayMarketMaker => decide
  | marketMaker => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderCapacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderCapacity

/-- Auction Event: one byte code -/
def AuctionEvent.codes : List UInt8 :=
  [0x53, 0x55, 0x45]

inductive AuctionEvent where
  | start -- Start
  | auctionUpdate -- Auction Update
  | endOfAuction -- End Of Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionEvent.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionEvent

def toByte : AuctionEvent → UInt8
  | .start => 0x53
  | .auctionUpdate => 0x55
  | .endOfAuction => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionEvent :=
  if byte = 0x53 then .start
  else if byte = 0x55 then .auctionUpdate
  else .endOfAuction

def ofByte (byte : UInt8) : AuctionEvent :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionEvent) : ofByte value.toByte = value := by
  cases value with
  | start => decide
  | auctionUpdate => decide
  | endOfAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionEvent) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionEvent × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionEvent) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AuctionEvent) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionEvent

/-- System Event Message: 13 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 48
  eventCode : EventCode
  currentYear : BitVec 16
  currentMonth : BitVec 8
  currentDay : BitVec 8
  version : BitVec 8
  subversion : BitVec 8
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 2 message.currentYear
    ++ (encodeUInt 1 message.currentMonth
    ++ (encodeUInt 1 message.currentDay
    ++ (encodeUInt 1 message.version
    ++ (encodeUInt 1 message.subversion))))))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (currentYear, bytes) ← decodeUInt 2 bytes
  let (currentMonth, bytes) ← decodeUInt 1 bytes
  let (currentDay, bytes) ← decodeUInt 1 bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (subversion, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, eventCode, currentYear, currentMonth, currentDay, version, subversion }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 13 := by
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
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
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

end SystemEventMessage

/-- Option Directory Message: 49 bytes -/
structure OptionDirectoryMessage where
  timestamp : BitVec 48
  optionId : BitVec 32
  securitySymbol : Alpha 6
  expirationYear : BitVec 8
  expirationMonth : BitVec 8
  expirationDay : BitVec 8
  strikePrice : BitVec 64
  optionType : OptionType
  source : BitVec 8
  underlyingSymbol : Alpha 13
  tradingType : TradingType
  contractSize : BitVec 16
  optionClosingType : OptionClosingType
  tradable : Tradable
  mpv : Mpv
  closingOnly : ClosingOnly
  deriving DecidableEq, Repr

namespace OptionDirectoryMessage

def encode (message : OptionDirectoryMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 1 message.expirationYear
    ++ (encodeUInt 1 message.expirationMonth
    ++ (encodeUInt 1 message.expirationDay
    ++ (encodeUInt 8 message.strikePrice
    ++ (OptionType.encode message.optionType
    ++ (encodeUInt 1 message.source
    ++ (Alpha.encode message.underlyingSymbol
    ++ (TradingType.encode message.tradingType
    ++ (encodeUInt 2 message.contractSize
    ++ (OptionClosingType.encode message.optionClosingType
    ++ (Tradable.encode message.tradable
    ++ (Mpv.encode message.mpv
    ++ (ClosingOnly.encode message.closingOnly)))))))))))))))

def decode (bytes : List UInt8) : Option (OptionDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 6 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  let (expirationMonth, bytes) ← decodeUInt 1 bytes
  let (expirationDay, bytes) ← decodeUInt 1 bytes
  let (strikePrice, bytes) ← decodeUInt 8 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (source, bytes) ← decodeUInt 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (tradingType, bytes) ← TradingType.decode bytes
  let (contractSize, bytes) ← decodeUInt 2 bytes
  let (optionClosingType, bytes) ← OptionClosingType.decode bytes
  let (tradable_, bytes) ← Tradable.decode bytes
  let (mpv, bytes) ← Mpv.decode bytes
  let (closingOnly, bytes) ← ClosingOnly.decode bytes
  pure ({ timestamp, optionId, securitySymbol, expirationYear, expirationMonth, expirationDay, strikePrice, optionType, source, underlyingSymbol, tradingType, contractSize, optionClosingType, tradable := tradable_, mpv, closingOnly }, bytes)

@[simp] theorem encode_length (message : OptionDirectoryMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, TradingType.encode_length, OptionClosingType.encode_length, Tradable.encode_length, Mpv.encode_length, ClosingOnly.encode_length]

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
  rw [List.append_assoc, TradingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionClosingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tradable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Mpv.decode_encode, some_bind]
  dsimp only
  rw [ClosingOnly.decode_encode, some_bind]
  rfl

end OptionDirectoryMessage

/-- Trading Action Message: 11 bytes -/
structure TradingActionMessage where
  timestamp : BitVec 48
  optionId : BitVec 32
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace TradingActionMessage

def encode (message : TradingActionMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (CurrentTradingState.encode message.currentTradingState))

def decode (bytes : List UInt8) : Option (TradingActionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ timestamp, optionId, currentTradingState }, bytes)

@[simp] theorem encode_length (message : TradingActionMessage) : (encode message).length = 11 := by
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

/-- Security Open Closed Message: 11 bytes -/
structure SecurityOpenClosedMessage where
  timestamp : BitVec 48
  optionId : BitVec 32
  openState : OpenState
  deriving DecidableEq, Repr

namespace SecurityOpenClosedMessage

def encode (message : SecurityOpenClosedMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (OpenState.encode message.openState))

def decode (bytes : List UInt8) : Option (SecurityOpenClosedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (openState, bytes) ← OpenState.decode bytes
  pure ({ timestamp, optionId, openState }, bytes)

@[simp] theorem encode_length (message : SecurityOpenClosedMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OpenState.encode_length]

theorem encode_length_pos (message : SecurityOpenClosedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityOpenClosedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OpenState.decode_encode, some_bind]
  rfl

end SecurityOpenClosedMessage

/-- Opening Imbalance Message: 23 bytes -/
structure OpeningImbalanceMessage where
  timestamp : BitVec 48
  optionId : BitVec 32
  pairedContracts : BitVec 32
  imbalanceDirection : ImbalanceDirection
  imbalancePrice : BitVec 32
  imbalanceVolume : BitVec 32
  deriving DecidableEq, Repr

namespace OpeningImbalanceMessage

def encode (message : OpeningImbalanceMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.pairedContracts
    ++ (ImbalanceDirection.encode message.imbalanceDirection
    ++ (encodeUInt 4 message.imbalancePrice
    ++ (encodeUInt 4 message.imbalanceVolume)))))

def decode (bytes : List UInt8) : Option (OpeningImbalanceMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (pairedContracts, bytes) ← decodeUInt 4 bytes
  let (imbalanceDirection, bytes) ← ImbalanceDirection.decode bytes
  let (imbalancePrice, bytes) ← decodeUInt 4 bytes
  let (imbalanceVolume, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, optionId, pairedContracts, imbalanceDirection, imbalancePrice, imbalanceVolume }, bytes)

@[simp] theorem encode_length (message : OpeningImbalanceMessage) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ImbalanceDirection.encode_length]

theorem encode_length_pos (message : OpeningImbalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpeningImbalanceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ImbalanceDirection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpeningImbalanceMessage

/-- Order On Book Message: 40 bytes -/
structure OrderOnBookMessage where
  timestamp : BitVec 48
  optionId : BitVec 32
  orderType : OrderType
  side : Side
  price : BitVec 32
  size : BitVec 32
  execFlag : ExecFlag
  orderCapacity : OrderCapacity
  ownerId : Alpha 6
  giveup : Alpha 6
  cmta : Alpha 6
  deriving DecidableEq, Repr

namespace OrderOnBookMessage

def encode (message : OrderOnBookMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (OrderType.encode message.orderType
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.size
    ++ (ExecFlag.encode message.execFlag
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (Alpha.encode message.ownerId
    ++ (Alpha.encode message.giveup
    ++ (Alpha.encode message.cmta))))))))))

def decode (bytes : List UInt8) : Option (OrderOnBookMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (size, bytes) ← decodeUInt 4 bytes
  let (execFlag, bytes) ← ExecFlag.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (ownerId, bytes) ← Alpha.decode 6 bytes
  let (giveup, bytes) ← Alpha.decode 6 bytes
  let (cmta, bytes) ← Alpha.decode 6 bytes
  pure ({ timestamp, optionId, orderType, side, price, size, execFlag, orderCapacity, ownerId, giveup, cmta }, bytes)

@[simp] theorem encode_length (message : OrderOnBookMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OrderType.encode_length, Side.encode_length, ExecFlag.encode_length, OrderCapacity.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderOnBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderOnBookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderOnBookMessage

/-- Auction Response: 8 bytes -/
structure AuctionResponse where
  responsePrice : BitVec 32
  responseSize : BitVec 32
  deriving DecidableEq, Repr

namespace AuctionResponse

def encode (message : AuctionResponse) : List UInt8 :=
  encodeUInt 4 message.responsePrice
    ++ (encodeUInt 4 message.responseSize)

def decode (bytes : List UInt8) : Option (AuctionResponse × List UInt8) := do
  let (responsePrice, bytes) ← decodeUInt 4 bytes
  let (responseSize, bytes) ← decodeUInt 4 bytes
  pure ({ responsePrice, responseSize }, bytes)

@[simp] theorem encode_length (message : AuctionResponse) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AuctionResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AuctionResponse

/-- Auction Message -/
structure AuctionMessage where
  timestamp : BitVec 48
  optionId : BitVec 32
  auctionId : BitVec 32
  orderType : OrderType
  side : Side
  price : BitVec 32
  size : BitVec 32
  execFlag : ExecFlag
  orderCapacity : OrderCapacity
  ownerId : Alpha 6
  giveup : Alpha 6
  cmta : Alpha 6
  auctionEvent : AuctionEvent
  auctionResponse : Bounded 1 AuctionResponse
  deriving DecidableEq, Repr

namespace AuctionMessage

def encode (message : AuctionMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.auctionId
    ++ (OrderType.encode message.orderType
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.size
    ++ (ExecFlag.encode message.execFlag
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (Alpha.encode message.ownerId
    ++ (Alpha.encode message.giveup
    ++ (Alpha.encode message.cmta
    ++ (AuctionEvent.encode message.auctionEvent
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.auctionResponse.val.length)
    ++ (encodeMany AuctionResponse.encode message.auctionResponse.val))))))))))))))

def decode (bytes : List UInt8) : Option (AuctionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (size, bytes) ← decodeUInt 4 bytes
  let (execFlag, bytes) ← ExecFlag.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (ownerId, bytes) ← Alpha.decode 6 bytes
  let (giveup, bytes) ← Alpha.decode 6 bytes
  let (cmta, bytes) ← Alpha.decode 6 bytes
  let (auctionEvent, bytes) ← AuctionEvent.decode bytes
  let (numberOfResponses, bytes) ← decodeUInt 1 bytes
  let (auctionResponse_, bytes) ← decodeMany AuctionResponse.decode numberOfResponses.toNat bytes
  if fits_auctionResponse : auctionResponse_.length < 256 ^ 1 then
    pure ({ timestamp, optionId, auctionId, orderType, side, price, size, execFlag, orderCapacity, ownerId, giveup, cmta, auctionEvent, auctionResponse := ⟨auctionResponse_, fits_auctionResponse⟩ }, bytes)
  else none

theorem encode_length_pos (message : AuctionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AuctionMessage) : (encode message).length ≤ 2086 := by
  have bound_auctionResponse := message.auctionResponse.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderType.encode_length, Side.encode_length, ExecFlag.encode_length, OrderCapacity.encode_length, Alpha.encode_length, AuctionEvent.encode_length, encodeMany_length_const AuctionResponse.encode 8 AuctionResponse.encode_length]
  omega

@[simp] theorem decode_encode (message : AuctionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionEvent.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 AuctionResponse.encode AuctionResponse.decode AuctionResponse.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.auctionResponse.length_lt]
  rfl

end AuctionMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- 'S' 0x53
  | optionDirectoryMessage (message : OptionDirectoryMessage) -- 'D' 0x44
  | tradingActionMessage (message : TradingActionMessage) -- 'H' 0x48
  | securityOpenClosedMessage (message : SecurityOpenClosedMessage) -- 'O' 0x4F
  | openingImbalanceMessage (message : OpeningImbalanceMessage) -- 'N' 0x4E
  | orderOnBookMessage (message : OrderOnBookMessage) -- 'B' 0x42
  | auctionMessage (message : AuctionMessage) -- 'A' 0x41
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .optionDirectoryMessage _ => 68
  | .tradingActionMessage _ => 72
  | .securityOpenClosedMessage _ => 79
  | .openingImbalanceMessage _ => 78
  | .orderOnBookMessage _ => 66
  | .auctionMessage _ => 65

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .optionDirectoryMessage message => OptionDirectoryMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .securityOpenClosedMessage message => SecurityOpenClosedMessage.encode message
  | .openingImbalanceMessage message => OpeningImbalanceMessage.encode message
  | .orderOnBookMessage message => OrderOnBookMessage.encode message
  | .auctionMessage message => AuctionMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 2086 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | optionDirectoryMessage inner =>
    simp only [encode, OptionDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [encode, TradingActionMessage.encode_length]
    omega
  | securityOpenClosedMessage inner =>
    simp only [encode, SecurityOpenClosedMessage.encode_length]
    omega
  | openingImbalanceMessage inner =>
    simp only [encode, OpeningImbalanceMessage.encode_length]
    omega
  | orderOnBookMessage inner =>
    simp only [encode, OrderOnBookMessage.encode_length]
    omega
  | auctionMessage inner =>
    have bound_inner := AuctionMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 68 then (OptionDirectoryMessage.decode bytes).map fun (message, rest) => (.optionDirectoryMessage message, rest)
  else if tag = 72 then (TradingActionMessage.decode bytes).map fun (message, rest) => (.tradingActionMessage message, rest)
  else if tag = 79 then (SecurityOpenClosedMessage.decode bytes).map fun (message, rest) => (.securityOpenClosedMessage message, rest)
  else if tag = 78 then (OpeningImbalanceMessage.decode bytes).map fun (message, rest) => (.openingImbalanceMessage message, rest)
  else if tag = 66 then (OrderOnBookMessage.decode bytes).map fun (message, rest) => (.orderOnBookMessage message, rest)
  else if tag = 65 then (AuctionMessage.decode bytes).map fun (message, rest) => (.auctionMessage message, rest)
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
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | optionDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OptionDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingActionMessage.encode_length]
    omega
  | securityOpenClosedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityOpenClosedMessage.encode_length]
    omega
  | openingImbalanceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OpeningImbalanceMessage.encode_length]
    omega
  | orderOnBookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderOnBookMessage.encode_length]
    omega
  | auctionMessage inner =>
    have bound_inner := AuctionMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUInt_length]
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

end Omi.NasdaqIseoptionsOrderfeedItchV11
