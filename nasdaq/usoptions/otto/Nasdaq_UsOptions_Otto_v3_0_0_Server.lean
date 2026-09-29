import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Ouch to Trade Options v3.0.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqUsoptionsOttoOuchV300Server

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
  [0x4F, 0x53, 0x50, 0x44, 0x51, 0x57, 0x4E, 0x4C, 0x45, 0x43]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfPreTradingOpeningProcess -- Start Of Pre Trading Opening Process
  | endOfPreTrading -- End Of Pre Trading
  | startOfOpeningProcess -- Start Of Opening Process
  | endOfWcoEarlyClosing -- End Of Wco Early Closing
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
  | .startOfPreTradingOpeningProcess => 0x50
  | .endOfPreTrading => 0x44
  | .startOfOpeningProcess => 0x51
  | .endOfWcoEarlyClosing => 0x57
  | .endOfNormalHoursProcessing => 0x4E
  | .endOfLateHoursProcessing => 0x4C
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x50 then .startOfPreTradingOpeningProcess
  else if byte = 0x44 then .endOfPreTrading
  else if byte = 0x51 then .startOfOpeningProcess
  else if byte = 0x57 then .endOfWcoEarlyClosing
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
  | startOfPreTradingOpeningProcess => decide
  | endOfPreTrading => decide
  | startOfOpeningProcess => decide
  | endOfWcoEarlyClosing => decide
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

/-- Closing Type: one byte code -/
def ClosingType.codes : List UInt8 :=
  [0x4E, 0x4C, 0x57, 0x45]

inductive ClosingType where
  | normalHours -- Normal Hours
  | lateHours -- Late Hours
  | wcoEarlyClosing -- Wco Early Closing
  | extendedClose -- Extended Close
  | unlisted (byte : { byte : UInt8 // byte ∉ ClosingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClosingType

def toByte : ClosingType → UInt8
  | .normalHours => 0x4E
  | .lateHours => 0x4C
  | .wcoEarlyClosing => 0x57
  | .extendedClose => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClosingType :=
  if byte = 0x4E then .normalHours
  else if byte = 0x4C then .lateHours
  else if byte = 0x57 then .wcoEarlyClosing
  else .extendedClose

def ofByte (byte : UInt8) : ClosingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClosingType) : ofByte value.toByte = value := by
  cases value with
  | normalHours => decide
  | lateHours => decide
  | wcoEarlyClosing => decide
  | extendedClose => decide
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

/-- Closing Only: one byte code -/
def ClosingOnly.codes : List UInt8 :=
  [0x4E, 0x59]

inductive ClosingOnly where
  | unrestricted -- Unrestricted
  | closingPositionOnly -- Closing Position Only
  | unlisted (byte : { byte : UInt8 // byte ∉ ClosingOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClosingOnly

def toByte : ClosingOnly → UInt8
  | .unrestricted => 0x4E
  | .closingPositionOnly => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClosingOnly :=
  if byte = 0x4E then .unrestricted
  else .closingPositionOnly

def ofByte (byte : UInt8) : ClosingOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClosingOnly) : ofByte value.toByte = value := by
  cases value with
  | unrestricted => decide
  | closingPositionOnly => decide
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

/-- Leg Type: one byte code -/
def LegType.codes : List UInt8 :=
  [0x4F, 0x53]

inductive LegType where
  | option -- Option
  | stock -- Stock
  | unlisted (byte : { byte : UInt8 // byte ∉ LegType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegType

def toByte : LegType → UInt8
  | .option => 0x4F
  | .stock => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegType :=
  if byte = 0x4F then .option
  else .stock

def ofByte (byte : UInt8) : LegType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegType) : ofByte value.toByte = value := by
  cases value with
  | option => decide
  | stock => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegType

/-- Leg Side: one byte code -/
def LegSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive LegSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide

def toByte : LegSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : LegSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSide

/-- Trading State: one byte code -/
def TradingState.codes : List UInt8 :=
  [0x48, 0x54]

inductive TradingState where
  | halted -- Halted
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .halted => 0x48
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x48 then .halted
  else .trading

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | trading => decide
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

/-- Instrument Type: one byte code -/
def InstrumentType.codes : List UInt8 :=
  [0x41, 0x4F, 0x43, 0x53]

inductive InstrumentType where
  | all -- All
  | simpleInstrument -- Simple Instrument
  | standardCombination -- Standard Combination
  | stockCombination -- Stock Combination
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .all => 0x41
  | .simpleInstrument => 0x4F
  | .standardCombination => 0x43
  | .stockCombination => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentType :=
  if byte = 0x41 then .all
  else if byte = 0x4F then .simpleInstrument
  else if byte = 0x43 then .standardCombination
  else .stockCombination

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | all => decide
  | simpleInstrument => decide
  | standardCombination => decide
  | stockCombination => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InstrumentType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentType

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x4C, 0x4D, 0x4E]

inductive OrderType where
  | limit -- Limit
  | market -- Market
  | notDisclosed -- Not Disclosed
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .limit => 0x4C
  | .market => 0x4D
  | .notDisclosed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x4C then .limit
  else if byte = 0x4D then .market
  else .notDisclosed

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | limit => decide
  | market => decide
  | notDisclosed => decide
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
  [0x42, 0x53, 0x4F, 0x4E]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | offer -- Offer
  | notDisclosed -- Not Disclosed
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .offer => 0x4F
  | .notDisclosed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x4F then .offer
  else .notDisclosed

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | offer => decide
  | notDisclosed => decide
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
  [0x30, 0x31]

inductive ExecFlag where
  | none_ -- None
  | aon -- Aon
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecFlag

def toByte : ExecFlag → UInt8
  | .none_ => 0x30
  | .aon => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecFlag :=
  if byte = 0x30 then .none_
  else .aon

def ofByte (byte : UInt8) : ExecFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecFlag) : ofByte value.toByte = value := by
  cases value with
  | none_ => decide
  | aon => decide
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
  [0x43, 0x46, 0x4D, 0x4F, 0x50, 0x42, 0x4A, 0x52, 0x20]

inductive OrderCapacity where
  | customer -- Customer
  | firm -- Firm
  | marketMaker -- Market Maker
  | otherExchangeRegisteredMarketMaker -- Other Exchange Registered Market Maker
  | professionalCustomer -- Professional Customer
  | brokerDealer -- Broker Dealer
  | jointBackOffice -- Joint Back Office
  | retail -- Retail
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderCapacity

def toByte : OrderCapacity → UInt8
  | .customer => 0x43
  | .firm => 0x46
  | .marketMaker => 0x4D
  | .otherExchangeRegisteredMarketMaker => 0x4F
  | .professionalCustomer => 0x50
  | .brokerDealer => 0x42
  | .jointBackOffice => 0x4A
  | .retail => 0x52
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderCapacity :=
  if byte = 0x43 then .customer
  else if byte = 0x46 then .firm
  else if byte = 0x4D then .marketMaker
  else if byte = 0x4F then .otherExchangeRegisteredMarketMaker
  else if byte = 0x50 then .professionalCustomer
  else if byte = 0x42 then .brokerDealer
  else if byte = 0x4A then .jointBackOffice
  else if byte = 0x52 then .retail
  else .notApplicable

def ofByte (byte : UInt8) : OrderCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderCapacity) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | firm => decide
  | marketMaker => decide
  | otherExchangeRegisteredMarketMaker => decide
  | professionalCustomer => decide
  | brokerDealer => decide
  | jointBackOffice => decide
  | retail => decide
  | notApplicable => decide
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

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x42, 0x45, 0x46, 0x4F, 0x58, 0x50, 0x48, 0x53, 0x4E]

inductive AuctionType where
  | blockOrderAuction -- Block Order Auction
  | complexExposureAuction -- Complex Exposure Auction
  | simpleExposureOrder -- Simple Exposure Order
  | openingAuction -- Opening Auction
  | flexAuction -- Flex Auction
  | pimPixlAuction -- Pim Pixl Auction
  | facilitationAuction -- Facilitation Auction
  | solicitationAuction -- Solicitation Auction
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .blockOrderAuction => 0x42
  | .complexExposureAuction => 0x45
  | .simpleExposureOrder => 0x46
  | .openingAuction => 0x4F
  | .flexAuction => 0x58
  | .pimPixlAuction => 0x50
  | .facilitationAuction => 0x48
  | .solicitationAuction => 0x53
  | .none_ => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x42 then .blockOrderAuction
  else if byte = 0x45 then .complexExposureAuction
  else if byte = 0x46 then .simpleExposureOrder
  else if byte = 0x4F then .openingAuction
  else if byte = 0x58 then .flexAuction
  else if byte = 0x50 then .pimPixlAuction
  else if byte = 0x48 then .facilitationAuction
  else if byte = 0x53 then .solicitationAuction
  else .none_

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | blockOrderAuction => decide
  | complexExposureAuction => decide
  | simpleExposureOrder => decide
  | openingAuction => decide
  | flexAuction => decide
  | pimPixlAuction => decide
  | facilitationAuction => decide
  | solicitationAuction => decide
  | none_ => decide
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

/-- Alo Inst: one byte code -/
def AloInst.codes : List UInt8 :=
  [0x4E, 0x59]

inductive AloInst where
  | notAlo -- Not Alo
  | alo -- Alo
  | unlisted (byte : { byte : UInt8 // byte ∉ AloInst.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AloInst

def toByte : AloInst → UInt8
  | .notAlo => 0x4E
  | .alo => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AloInst :=
  if byte = 0x4E then .notAlo
  else .alo

def ofByte (byte : UInt8) : AloInst :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AloInst) : ofByte value.toByte = value := by
  cases value with
  | notAlo => decide
  | alo => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AloInst) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AloInst × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AloInst) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AloInst) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AloInst

/-- Iso: one byte code -/
def Iso.codes : List UInt8 :=
  [0x4E, 0x49]

inductive Iso where
  | notIso -- Not Iso
  | iso -- Iso
  | unlisted (byte : { byte : UInt8 // byte ∉ Iso.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Iso

def toByte : Iso → UInt8
  | .notIso => 0x4E
  | .iso => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Iso :=
  if byte = 0x4E then .notIso
  else .iso

def ofByte (byte : UInt8) : Iso :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Iso) : ofByte value.toByte = value := by
  cases value with
  | notIso => decide
  | iso => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Iso) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Iso × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Iso) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Iso) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Iso

/-- Tif: one byte code -/
def Tif.codes : List UInt8 :=
  [0x44, 0x46, 0x49]

inductive Tif where
  | day -- Day
  | fok -- Fok
  | ioc -- Ioc
  | unlisted (byte : { byte : UInt8 // byte ∉ Tif.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tif

def toByte : Tif → UInt8
  | .day => 0x44
  | .fok => 0x46
  | .ioc => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tif :=
  if byte = 0x44 then .day
  else if byte = 0x46 then .fok
  else .ioc

def ofByte (byte : UInt8) : Tif :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tif) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | fok => decide
  | ioc => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Tif) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Tif × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Tif) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Tif) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Tif

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x43, 0x46, 0x4D, 0x4F, 0x50, 0x42, 0x4A, 0x52, 0x20]

inductive Capacity where
  | customer -- Customer
  | firm -- Firm
  | marketMaker -- Market Maker
  | otherExchangeRegisteredMarketMaker -- Other Exchange Registered Market Maker
  | professionalCustomer -- Professional Customer
  | brokerDealer -- Broker Dealer
  | jointBackOffice -- Joint Back Office
  | retail -- Retail
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .customer => 0x43
  | .firm => 0x46
  | .marketMaker => 0x4D
  | .otherExchangeRegisteredMarketMaker => 0x4F
  | .professionalCustomer => 0x50
  | .brokerDealer => 0x42
  | .jointBackOffice => 0x4A
  | .retail => 0x52
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x43 then .customer
  else if byte = 0x46 then .firm
  else if byte = 0x4D then .marketMaker
  else if byte = 0x4F then .otherExchangeRegisteredMarketMaker
  else if byte = 0x50 then .professionalCustomer
  else if byte = 0x42 then .brokerDealer
  else if byte = 0x4A then .jointBackOffice
  else if byte = 0x52 then .retail
  else .notApplicable

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | firm => decide
  | marketMaker => decide
  | otherExchangeRegisteredMarketMaker => decide
  | professionalCustomer => decide
  | brokerDealer => decide
  | jointBackOffice => decide
  | retail => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Capacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Capacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Capacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Capacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Capacity

/-- Price Protection: one byte code -/
def PriceProtection.codes : List UInt8 :=
  [0x4C, 0x4E]

inductive PriceProtection where
  | local_ -- Local
  | national -- National
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceProtection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceProtection

def toByte : PriceProtection → UInt8
  | .local_ => 0x4C
  | .national => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceProtection :=
  if byte = 0x4C then .local_
  else .national

def ofByte (byte : UInt8) : PriceProtection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceProtection) : ofByte value.toByte = value := by
  cases value with
  | local_ => decide
  | national => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceProtection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceProtection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceProtection) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceProtection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceProtection

/-- Display When: one byte code -/
def DisplayWhen.codes : List UInt8 :=
  [0x49, 0x45, 0x4E]

inductive DisplayWhen where
  | immediate -- Immediate
  | exhaust -- Exhaust
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ DisplayWhen.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DisplayWhen

def toByte : DisplayWhen → UInt8
  | .immediate => 0x49
  | .exhaust => 0x45
  | .notApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DisplayWhen :=
  if byte = 0x49 then .immediate
  else if byte = 0x45 then .exhaust
  else .notApplicable

def ofByte (byte : UInt8) : DisplayWhen :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DisplayWhen) : ofByte value.toByte = value := by
  cases value with
  | immediate => decide
  | exhaust => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DisplayWhen) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DisplayWhen × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DisplayWhen) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DisplayWhen) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DisplayWhen

/-- Display Method: one byte code -/
def DisplayMethod.codes : List UInt8 :=
  [0x49, 0x52, 0x4E]

inductive DisplayMethod where
  | initial -- Initial
  | random -- Random
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ DisplayMethod.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DisplayMethod

def toByte : DisplayMethod → UInt8
  | .initial => 0x49
  | .random => 0x52
  | .none_ => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DisplayMethod :=
  if byte = 0x49 then .initial
  else if byte = 0x52 then .random
  else .none_

def ofByte (byte : UInt8) : DisplayMethod :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DisplayMethod) : ofByte value.toByte = value := by
  cases value with
  | initial => decide
  | random => decide
  | none_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DisplayMethod) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DisplayMethod × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DisplayMethod) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DisplayMethod) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DisplayMethod

/-- Stock Leg Short Sale: one byte code -/
def StockLegShortSale.codes : List UInt8 :=
  [0x4E, 0x48, 0x45]

inductive StockLegShortSale where
  | notApplicable -- Not Applicable
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ StockLegShortSale.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StockLegShortSale

def toByte : StockLegShortSale → UInt8
  | .notApplicable => 0x4E
  | .sellShort => 0x48
  | .sellShortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StockLegShortSale :=
  if byte = 0x4E then .notApplicable
  else if byte = 0x48 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : StockLegShortSale :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StockLegShortSale) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | sellShort => decide
  | sellShortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StockLegShortSale) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StockLegShortSale × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StockLegShortSale) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StockLegShortSale) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StockLegShortSale

/-- Stock Capacity: one byte code -/
def StockCapacity.codes : List UInt8 :=
  [0x50, 0x41, 0x52, 0x20]

inductive StockCapacity where
  | principal -- Principal
  | agency -- Agency
  | risklessPrincipal -- Riskless Principal
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ StockCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StockCapacity

def toByte : StockCapacity → UInt8
  | .principal => 0x50
  | .agency => 0x41
  | .risklessPrincipal => 0x52
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StockCapacity :=
  if byte = 0x50 then .principal
  else if byte = 0x41 then .agency
  else if byte = 0x52 then .risklessPrincipal
  else .notApplicable

def ofByte (byte : UInt8) : StockCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StockCapacity) : ofByte value.toByte = value := by
  cases value with
  | principal => decide
  | agency => decide
  | risklessPrincipal => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StockCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StockCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StockCapacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StockCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StockCapacity

/-- Session Eligibility: one byte code -/
def SessionEligibility.codes : List UInt8 :=
  [0x52, 0x41, 0x45]

inductive SessionEligibility where
  | regularSession -- Regular Session
  | allSessions -- All Sessions
  | extendedClose -- Extended Close
  | unlisted (byte : { byte : UInt8 // byte ∉ SessionEligibility.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SessionEligibility

def toByte : SessionEligibility → UInt8
  | .regularSession => 0x52
  | .allSessions => 0x41
  | .extendedClose => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SessionEligibility :=
  if byte = 0x52 then .regularSession
  else if byte = 0x41 then .allSessions
  else .extendedClose

def ofByte (byte : UInt8) : SessionEligibility :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SessionEligibility) : ofByte value.toByte = value := by
  cases value with
  | regularSession => decide
  | allSessions => decide
  | extendedClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SessionEligibility) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SessionEligibility × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SessionEligibility) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SessionEligibility) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SessionEligibility

/-- Cancel Reason: one byte code -/
def CancelReason.codes : List UInt8 :=
  [0x55, 0x49, 0x53, 0x44, 0x51, 0x42, 0x41, 0x4B, 0x43, 0x4F, 0x50, 0x5A]

inductive CancelReason where
  | userRequested -- User Requested
  | immediateOrCancel -- Immediate Or Cancel
  | supervisory -- Supervisory
  | regulatoryRestriction -- Regulatory Restriction
  | antiInternalize -- Anti Internalize
  | aloNotDisplayable -- Alo Not Displayable
  | unexecutedAuctionResponse -- Unexecuted Auction Response
  | killSwitch -- Kill Switch
  | cancelOnDisconnect -- Cancel On Disconnect
  | openDelayTimer -- Open Delay Timer
  | atrLimit -- Atr Limit
  | rejectedCancelReplace -- Rejected Cancel Replace
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelReason

def toByte : CancelReason → UInt8
  | .userRequested => 0x55
  | .immediateOrCancel => 0x49
  | .supervisory => 0x53
  | .regulatoryRestriction => 0x44
  | .antiInternalize => 0x51
  | .aloNotDisplayable => 0x42
  | .unexecutedAuctionResponse => 0x41
  | .killSwitch => 0x4B
  | .cancelOnDisconnect => 0x43
  | .openDelayTimer => 0x4F
  | .atrLimit => 0x50
  | .rejectedCancelReplace => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelReason :=
  if byte = 0x55 then .userRequested
  else if byte = 0x49 then .immediateOrCancel
  else if byte = 0x53 then .supervisory
  else if byte = 0x44 then .regulatoryRestriction
  else if byte = 0x51 then .antiInternalize
  else if byte = 0x42 then .aloNotDisplayable
  else if byte = 0x41 then .unexecutedAuctionResponse
  else if byte = 0x4B then .killSwitch
  else if byte = 0x43 then .cancelOnDisconnect
  else if byte = 0x4F then .openDelayTimer
  else if byte = 0x50 then .atrLimit
  else .rejectedCancelReplace

def ofByte (byte : UInt8) : CancelReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelReason) : ofByte value.toByte = value := by
  cases value with
  | userRequested => decide
  | immediateOrCancel => decide
  | supervisory => decide
  | regulatoryRestriction => decide
  | antiInternalize => decide
  | aloNotDisplayable => decide
  | unexecutedAuctionResponse => decide
  | killSwitch => decide
  | cancelOnDisconnect => decide
  | openDelayTimer => decide
  | atrLimit => decide
  | rejectedCancelReplace => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CancelReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelReason

/-- Ord Exec Type: one byte code -/
def OrdExecType.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44]

inductive OrdExecType where
  | simpleInstrument -- Simple Instrument
  | complexInstrument -- Complex Instrument
  | complexOptionLeg -- Complex Option Leg
  | complexStockLeg -- Complex Stock Leg
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdExecType

def toByte : OrdExecType → UInt8
  | .simpleInstrument => 0x41
  | .complexInstrument => 0x42
  | .complexOptionLeg => 0x43
  | .complexStockLeg => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdExecType :=
  if byte = 0x41 then .simpleInstrument
  else if byte = 0x42 then .complexInstrument
  else if byte = 0x43 then .complexOptionLeg
  else .complexStockLeg

def ofByte (byte : UInt8) : OrdExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdExecType) : ofByte value.toByte = value := by
  cases value with
  | simpleInstrument => decide
  | complexInstrument => decide
  | complexOptionLeg => decide
  | complexStockLeg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdExecType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdExecType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdExecType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrdExecType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdExecType

/-- Trans Type: one byte code -/
def TransType.codes : List UInt8 :=
  [0x41, 0x42, 0x43]

inductive TransType where
  | newTrade -- New Trade
  | tradeBusted -- Trade Busted
  | modifiedTrade -- Modified Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TransType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransType

def toByte : TransType → UInt8
  | .newTrade => 0x41
  | .tradeBusted => 0x42
  | .modifiedTrade => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransType :=
  if byte = 0x41 then .newTrade
  else if byte = 0x42 then .tradeBusted
  else .modifiedTrade

def ofByte (byte : UInt8) : TransType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransType) : ofByte value.toByte = value := by
  cases value with
  | newTrade => decide
  | tradeBusted => decide
  | modifiedTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TransType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransType

/-- Event Source: one byte code -/
def EventSource.codes : List UInt8 :=
  [0x41, 0x4D, 0x55, 0x43, 0x45, 0x42]

inductive EventSource where
  | matchingEngine -- Matching Engine
  | manualTradeEntry -- Manual Trade Entry
  | tradeModificationUser -- Trade Modification User
  | tradeModificationContraSideUser -- Trade Modification Contra Side User
  | tradeModificationExchange -- Trade Modification Exchange
  | tradeBustExchange -- Trade Bust Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ EventSource.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventSource

def toByte : EventSource → UInt8
  | .matchingEngine => 0x41
  | .manualTradeEntry => 0x4D
  | .tradeModificationUser => 0x55
  | .tradeModificationContraSideUser => 0x43
  | .tradeModificationExchange => 0x45
  | .tradeBustExchange => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventSource :=
  if byte = 0x41 then .matchingEngine
  else if byte = 0x4D then .manualTradeEntry
  else if byte = 0x55 then .tradeModificationUser
  else if byte = 0x43 then .tradeModificationContraSideUser
  else if byte = 0x45 then .tradeModificationExchange
  else .tradeBustExchange

def ofByte (byte : UInt8) : EventSource :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventSource) : ofByte value.toByte = value := by
  cases value with
  | matchingEngine => decide
  | manualTradeEntry => decide
  | tradeModificationUser => decide
  | tradeModificationContraSideUser => decide
  | tradeModificationExchange => decide
  | tradeBustExchange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventSource) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventSource × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventSource) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventSource) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventSource

/-- Stock Venue: one byte code -/
def StockVenue.codes : List UInt8 :=
  [0x58]

inductive StockVenue where
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ StockVenue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StockVenue

def toByte : StockVenue → UInt8
  | .notApplicable => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : StockVenue :=
  .notApplicable

def ofByte (byte : UInt8) : StockVenue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StockVenue) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StockVenue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StockVenue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StockVenue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StockVenue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StockVenue

/-- Open Close: one byte code -/
def OpenClose.codes : List UInt8 :=
  [0x4F, 0x43, 0x20]

inductive OpenClose where
  | open_ -- Open
  | closed -- Closed
  | carryForward -- Carry Forward
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenClose.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenClose

def toByte : OpenClose → UInt8
  | .open_ => 0x4F
  | .closed => 0x43
  | .carryForward => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenClose :=
  if byte = 0x4F then .open_
  else if byte = 0x43 then .closed
  else .carryForward

def ofByte (byte : UInt8) : OpenClose :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenClose) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | closed => decide
  | carryForward => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenClose) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenClose × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenClose) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenClose) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenClose

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x41, 0x51, 0x43]

inductive CrossType where
  | auction -- Auction
  | qcc -- Qcc
  | ccc -- Ccc
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .auction => 0x41
  | .qcc => 0x51
  | .ccc => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x41 then .auction
  else if byte = 0x51 then .qcc
  else .ccc

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | auction => decide
  | qcc => decide
  | ccc => decide
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

/-- Primary Capacity: one byte code -/
def PrimaryCapacity.codes : List UInt8 :=
  [0x43, 0x46, 0x4D, 0x4F, 0x50, 0x42, 0x4A, 0x52, 0x20]

inductive PrimaryCapacity where
  | customer -- Customer
  | firm -- Firm
  | marketMaker -- Market Maker
  | otherExchangeRegisteredMarketMaker -- Other Exchange Registered Market Maker
  | professionalCustomer -- Professional Customer
  | brokerDealer -- Broker Dealer
  | jointBackOffice -- Joint Back Office
  | retail -- Retail
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ PrimaryCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrimaryCapacity

def toByte : PrimaryCapacity → UInt8
  | .customer => 0x43
  | .firm => 0x46
  | .marketMaker => 0x4D
  | .otherExchangeRegisteredMarketMaker => 0x4F
  | .professionalCustomer => 0x50
  | .brokerDealer => 0x42
  | .jointBackOffice => 0x4A
  | .retail => 0x52
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrimaryCapacity :=
  if byte = 0x43 then .customer
  else if byte = 0x46 then .firm
  else if byte = 0x4D then .marketMaker
  else if byte = 0x4F then .otherExchangeRegisteredMarketMaker
  else if byte = 0x50 then .professionalCustomer
  else if byte = 0x42 then .brokerDealer
  else if byte = 0x4A then .jointBackOffice
  else if byte = 0x52 then .retail
  else .notApplicable

def ofByte (byte : UInt8) : PrimaryCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrimaryCapacity) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | firm => decide
  | marketMaker => decide
  | otherExchangeRegisteredMarketMaker => decide
  | professionalCustomer => decide
  | brokerDealer => decide
  | jointBackOffice => decide
  | retail => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrimaryCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrimaryCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrimaryCapacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrimaryCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrimaryCapacity

/-- Primary Stock Leg Short Sale: one byte code -/
def PrimaryStockLegShortSale.codes : List UInt8 :=
  [0x4E, 0x48, 0x45]

inductive PrimaryStockLegShortSale where
  | notApplicable -- Not Applicable
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ PrimaryStockLegShortSale.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrimaryStockLegShortSale

def toByte : PrimaryStockLegShortSale → UInt8
  | .notApplicable => 0x4E
  | .sellShort => 0x48
  | .sellShortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrimaryStockLegShortSale :=
  if byte = 0x4E then .notApplicable
  else if byte = 0x48 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : PrimaryStockLegShortSale :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrimaryStockLegShortSale) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | sellShort => decide
  | sellShortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrimaryStockLegShortSale) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrimaryStockLegShortSale × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrimaryStockLegShortSale) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrimaryStockLegShortSale) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrimaryStockLegShortSale

/-- Contra Order Type: one byte code -/
def ContraOrderType.codes : List UInt8 :=
  [0x4C, 0x4D]

inductive ContraOrderType where
  | limit -- Limit
  | market -- Market
  | unlisted (byte : { byte : UInt8 // byte ∉ ContraOrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContraOrderType

def toByte : ContraOrderType → UInt8
  | .limit => 0x4C
  | .market => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContraOrderType :=
  if byte = 0x4C then .limit
  else .market

def ofByte (byte : UInt8) : ContraOrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContraOrderType) : ofByte value.toByte = value := by
  cases value with
  | limit => decide
  | market => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContraOrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContraOrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContraOrderType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ContraOrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContraOrderType

/-- Contra Capacity: one byte code -/
def ContraCapacity.codes : List UInt8 :=
  [0x43, 0x46, 0x4D, 0x4F, 0x50, 0x42, 0x4A, 0x52, 0x20]

inductive ContraCapacity where
  | customer -- Customer
  | firm -- Firm
  | marketMaker -- Market Maker
  | otherExchangeRegisteredMarketMaker -- Other Exchange Registered Market Maker
  | professionalCustomer -- Professional Customer
  | brokerDealer -- Broker Dealer
  | jointBackOffice -- Joint Back Office
  | retail -- Retail
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ ContraCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContraCapacity

def toByte : ContraCapacity → UInt8
  | .customer => 0x43
  | .firm => 0x46
  | .marketMaker => 0x4D
  | .otherExchangeRegisteredMarketMaker => 0x4F
  | .professionalCustomer => 0x50
  | .brokerDealer => 0x42
  | .jointBackOffice => 0x4A
  | .retail => 0x52
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContraCapacity :=
  if byte = 0x43 then .customer
  else if byte = 0x46 then .firm
  else if byte = 0x4D then .marketMaker
  else if byte = 0x4F then .otherExchangeRegisteredMarketMaker
  else if byte = 0x50 then .professionalCustomer
  else if byte = 0x42 then .brokerDealer
  else if byte = 0x4A then .jointBackOffice
  else if byte = 0x52 then .retail
  else .notApplicable

def ofByte (byte : UInt8) : ContraCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContraCapacity) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | firm => decide
  | marketMaker => decide
  | otherExchangeRegisteredMarketMaker => decide
  | professionalCustomer => decide
  | brokerDealer => decide
  | jointBackOffice => decide
  | retail => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContraCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContraCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContraCapacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ContraCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContraCapacity

/-- Contra Stock Leg Short Sale: one byte code -/
def ContraStockLegShortSale.codes : List UInt8 :=
  [0x4E, 0x48, 0x45]

inductive ContraStockLegShortSale where
  | notApplicable -- Not Applicable
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ ContraStockLegShortSale.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContraStockLegShortSale

def toByte : ContraStockLegShortSale → UInt8
  | .notApplicable => 0x4E
  | .sellShort => 0x48
  | .sellShortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContraStockLegShortSale :=
  if byte = 0x4E then .notApplicable
  else if byte = 0x48 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : ContraStockLegShortSale :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContraStockLegShortSale) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | sellShort => decide
  | sellShortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContraStockLegShortSale) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContraStockLegShortSale × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContraStockLegShortSale) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ContraStockLegShortSale) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContraStockLegShortSale

/-- Kill Action: one byte code -/
def KillAction.codes : List UInt8 :=
  [0x41, 0x52, 0x42]

inductive KillAction where
  | blockAndDelete -- Block And Delete
  | blockRemoved -- Block Removed
  | block -- Block
  | unlisted (byte : { byte : UInt8 // byte ∉ KillAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace KillAction

def toByte : KillAction → UInt8
  | .blockAndDelete => 0x41
  | .blockRemoved => 0x52
  | .block => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : KillAction :=
  if byte = 0x41 then .blockAndDelete
  else if byte = 0x52 then .blockRemoved
  else .block

def ofByte (byte : UInt8) : KillAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : KillAction) : ofByte value.toByte = value := by
  cases value with
  | blockAndDelete => decide
  | blockRemoved => decide
  | block => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : KillAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (KillAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : KillAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : KillAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end KillAction

/-- Pending Reason: one byte code -/
def PendingReason.codes : List UInt8 :=
  [0x41]

inductive PendingReason where
  | requestInProgress -- Request In Progress
  | unlisted (byte : { byte : UInt8 // byte ∉ PendingReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PendingReason

def toByte : PendingReason → UInt8
  | .requestInProgress => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : PendingReason :=
  .requestInProgress

def ofByte (byte : UInt8) : PendingReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PendingReason) : ofByte value.toByte = value := by
  cases value with
  | requestInProgress => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PendingReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PendingReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PendingReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PendingReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PendingReason

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
  timestamp : BitVec 64
  eventCode : EventCode
  version : BitVec 8
  subversion : BitVec 8
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 1 message.version
    ++ (encodeUInt 1 message.subversion)))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (subversion, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, eventCode, version, subversion }, bytes)

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
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Simple Instrument Directory Message: 69 bytes -/
structure SimpleInstrumentDirectoryMessage where
  timestamp : BitVec 64
  productId : BitVec 16
  productName : Alpha 13
  instrumentId : BitVec 32
  expirYear : BitVec 8
  expirMon : BitVec 8
  expirDay : BitVec 8
  strikePrice : BitVec 64
  optionType : OptionType
  closingType : ClosingType
  tradable : Tradable
  closingOnly : ClosingOnly
  contractSize : BitVec 16
  mpv : Mpv
  securitySymbol : Alpha 8
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace SimpleInstrumentDirectoryMessage

def encode (message : SimpleInstrumentDirectoryMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.productId
    ++ (Alpha.encode message.productName
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 1 message.expirYear
    ++ (encodeUInt 1 message.expirMon
    ++ (encodeUInt 1 message.expirDay
    ++ (encodeUInt 8 message.strikePrice
    ++ (OptionType.encode message.optionType
    ++ (ClosingType.encode message.closingType
    ++ (Tradable.encode message.tradable
    ++ (ClosingOnly.encode message.closingOnly
    ++ (encodeUInt 2 message.contractSize
    ++ (Mpv.encode message.mpv
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.reserved16)))))))))))))))

def decode (bytes : List UInt8) : Option (SimpleInstrumentDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (productId, bytes) ← decodeUInt 2 bytes
  let (productName, bytes) ← Alpha.decode 13 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (expirYear, bytes) ← decodeUInt 1 bytes
  let (expirMon, bytes) ← decodeUInt 1 bytes
  let (expirDay, bytes) ← decodeUInt 1 bytes
  let (strikePrice, bytes) ← decodeUInt 8 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (closingType, bytes) ← ClosingType.decode bytes
  let (tradable_, bytes) ← Tradable.decode bytes
  let (closingOnly, bytes) ← ClosingOnly.decode bytes
  let (contractSize, bytes) ← decodeUInt 2 bytes
  let (mpv, bytes) ← Mpv.decode bytes
  let (securitySymbol, bytes) ← Alpha.decode 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ timestamp, productId, productName, instrumentId, expirYear, expirMon, expirDay, strikePrice, optionType, closingType, tradable := tradable_, closingOnly, contractSize, mpv, securitySymbol, reserved16 }, bytes)

@[simp] theorem encode_length (message : SimpleInstrumentDirectoryMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, ClosingType.encode_length, Tradable.encode_length, ClosingOnly.encode_length, Mpv.encode_length]

theorem encode_length_pos (message : SimpleInstrumentDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleInstrumentDirectoryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClosingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tradable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClosingOnly.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Mpv.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleInstrumentDirectoryMessage

/-- Complex Directory Legs: 9 bytes -/
structure ComplexDirectoryLegs where
  legType : LegType
  legInstrumentId : BitVec 32
  legSide : LegSide
  legRatio : BitVec 16
  legId : BitVec 8
  deriving DecidableEq, Repr

namespace ComplexDirectoryLegs

def encode (message : ComplexDirectoryLegs) : List UInt8 :=
  LegType.encode message.legType
    ++ (encodeUInt 4 message.legInstrumentId
    ++ (LegSide.encode message.legSide
    ++ (encodeUInt 2 message.legRatio
    ++ (encodeUInt 1 message.legId))))

def decode (bytes : List UInt8) : Option (ComplexDirectoryLegs × List UInt8) := do
  let (legType, bytes) ← LegType.decode bytes
  let (legInstrumentId, bytes) ← decodeUInt 4 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (legRatio, bytes) ← decodeUInt 2 bytes
  let (legId, bytes) ← decodeUInt 1 bytes
  pure ({ legType, legInstrumentId, legSide, legRatio, legId }, bytes)

@[simp] theorem encode_length (message : ComplexDirectoryLegs) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, LegType.encode_length, encodeUInt_length, LegSide.encode_length]

theorem encode_length_pos (message : ComplexDirectoryLegs) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexDirectoryLegs) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LegType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ComplexDirectoryLegs

/-- Complex Instrument Directory Message -/
structure ComplexInstrumentDirectoryMessage where
  timestamp : BitVec 64
  productId : BitVec 16
  productName : Alpha 13
  instrumentId : BitVec 32
  reserved1 : Alpha 1
  complexDirectoryLegs : Bounded 1 ComplexDirectoryLegs
  deriving DecidableEq, Repr

namespace ComplexInstrumentDirectoryMessage

def encode (message : ComplexInstrumentDirectoryMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.productId
    ++ (Alpha.encode message.productName
    ++ (encodeUInt 4 message.instrumentId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.complexDirectoryLegs.val.length)
    ++ (encodeMany ComplexDirectoryLegs.encode message.complexDirectoryLegs.val))))))

def decode (bytes : List UInt8) : Option (ComplexInstrumentDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (productId, bytes) ← decodeUInt 2 bytes
  let (productName, bytes) ← Alpha.decode 13 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (numLegs, bytes) ← decodeUInt 1 bytes
  let (complexDirectoryLegs_, bytes) ← decodeMany ComplexDirectoryLegs.decode numLegs.toNat bytes
  if fits_complexDirectoryLegs : complexDirectoryLegs_.length < 256 ^ 1 then
    pure ({ timestamp, productId, productName, instrumentId, reserved1, complexDirectoryLegs := ⟨complexDirectoryLegs_, fits_complexDirectoryLegs⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexInstrumentDirectoryMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexInstrumentDirectoryMessage) : (encode message).length ≤ 2324 := by
  have bound_complexDirectoryLegs := message.complexDirectoryLegs.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const ComplexDirectoryLegs.encode 9 ComplexDirectoryLegs.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexInstrumentDirectoryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 ComplexDirectoryLegs.encode ComplexDirectoryLegs.decode ComplexDirectoryLegs.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.complexDirectoryLegs.length_lt]
  rfl

end ComplexInstrumentDirectoryMessage

/-- Instrument Trading Action Message: 15 bytes -/
structure InstrumentTradingActionMessage where
  timestamp : BitVec 64
  productId : BitVec 16
  instrumentId : BitVec 32
  tradingState : TradingState
  deriving DecidableEq, Repr

namespace InstrumentTradingActionMessage

def encode (message : InstrumentTradingActionMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.productId
    ++ (encodeUInt 4 message.instrumentId
    ++ (TradingState.encode message.tradingState)))

def decode (bytes : List UInt8) : Option (InstrumentTradingActionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (productId, bytes) ← decodeUInt 2 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  pure ({ timestamp, productId, instrumentId, tradingState }, bytes)

@[simp] theorem encode_length (message : InstrumentTradingActionMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradingState.encode_length]

theorem encode_length_pos (message : InstrumentTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TradingState.decode_encode, some_bind]
  rfl

end InstrumentTradingActionMessage

/-- Flex Dac Legs: 8 bytes -/
structure FlexDacLegs where
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace FlexDacLegs

def encode (message : FlexDacLegs) : List UInt8 :=
  Alpha.encode message.reserved8

def decode (bytes : List UInt8) : Option (FlexDacLegs × List UInt8) := do
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ reserved8 }, bytes)

@[simp] theorem encode_length (message : FlexDacLegs) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : FlexDacLegs) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FlexDacLegs) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end FlexDacLegs

/-- Auction Notification Message -/
structure AuctionNotificationMessage where
  timestamp : BitVec 64
  instrumentType : InstrumentType
  instrumentId : BitVec 32
  auctionId : BitVec 32
  orderType : OrderType
  side : Side
  price : BitVec 64
  quantity : BitVec 32
  execFlag : ExecFlag
  orderCapacity : OrderCapacity
  firmId : Alpha 4
  occAccount : BitVec 32
  cmta : BitVec 32
  auctionEvent : AuctionEvent
  auctionType : AuctionType
  auctionDuration : BitVec 32
  bestResponsePrice : BitVec 64
  bestResponseSize : BitVec 32
  reserved9 : Alpha 9
  flexDacLegs : Bounded 1 FlexDacLegs
  deriving DecidableEq, Repr

namespace AuctionNotificationMessage

def encode (message : AuctionNotificationMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.auctionId
    ++ (OrderType.encode message.orderType
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.quantity
    ++ (ExecFlag.encode message.execFlag
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 4 message.occAccount
    ++ (encodeUInt 4 message.cmta
    ++ (AuctionEvent.encode message.auctionEvent
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.auctionDuration
    ++ (encodeUInt 8 message.bestResponsePrice
    ++ (encodeUInt 4 message.bestResponseSize
    ++ (Alpha.encode message.reserved9
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.flexDacLegs.val.length)
    ++ (encodeMany FlexDacLegs.encode message.flexDacLegs.val))))))))))))))))))))

def decode (bytes : List UInt8) : Option (AuctionNotificationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (execFlag, bytes) ← ExecFlag.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (occAccount, bytes) ← decodeUInt 4 bytes
  let (cmta, bytes) ← decodeUInt 4 bytes
  let (auctionEvent, bytes) ← AuctionEvent.decode bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (auctionDuration, bytes) ← decodeUInt 4 bytes
  let (bestResponsePrice, bytes) ← decodeUInt 8 bytes
  let (bestResponseSize, bytes) ← decodeUInt 4 bytes
  let (reserved9, bytes) ← Alpha.decode 9 bytes
  let (numberOfFlexDacLegs, bytes) ← decodeUInt 1 bytes
  let (flexDacLegs_, bytes) ← decodeMany FlexDacLegs.decode numberOfFlexDacLegs.toNat bytes
  if fits_flexDacLegs : flexDacLegs_.length < 256 ^ 1 then
    pure ({ timestamp, instrumentType, instrumentId, auctionId, orderType, side, price, quantity, execFlag, orderCapacity, firmId, occAccount, cmta, auctionEvent, auctionType, auctionDuration, bestResponsePrice, bestResponseSize, reserved9, flexDacLegs := ⟨flexDacLegs_, fits_flexDacLegs⟩ }, bytes)
  else none

theorem encode_length_pos (message : AuctionNotificationMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AuctionNotificationMessage) : (encode message).length ≤ 2113 := by
  have bound_flexDacLegs := message.flexDacLegs.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, InstrumentType.encode_length, OrderType.encode_length, Side.encode_length, ExecFlag.encode_length, OrderCapacity.encode_length, Alpha.encode_length, AuctionEvent.encode_length, AuctionType.encode_length, encodeMany_length_const FlexDacLegs.encode 8 FlexDacLegs.encode_length]
  omega

@[simp] theorem decode_encode (message : AuctionNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionEvent.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
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
  rw [decodeMany_bounded 1 FlexDacLegs.encode FlexDacLegs.decode FlexDacLegs.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.flexDacLegs.length_lt]
  rfl

end AuctionNotificationMessage

/-- Flex Legs: 8 bytes -/
structure FlexLegs where
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace FlexLegs

def encode (message : FlexLegs) : List UInt8 :=
  Alpha.encode message.reserved8

def decode (bytes : List UInt8) : Option (FlexLegs × List UInt8) := do
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ reserved8 }, bytes)

@[simp] theorem encode_length (message : FlexLegs) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : FlexLegs) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FlexLegs) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end FlexLegs

/-- Order Accepted Long Form Message -/
structure OrderAcceptedLongFormMessage where
  timestamp : BitVec 64
  firmId : Alpha 4
  instrumentId : BitVec 32
  orderId : BitVec 64
  clOrdId : Alpha 16
  cmta : BitVec 32
  clearingAccount : Alpha 4
  occAccount : BitVec 32
  custAcct : Alpha 10
  preferredParty : Alpha 3
  aloInst : AloInst
  iso : Iso
  side : Side
  orderType : OrderType
  price : BitVec 64
  quantity : BitVec 32
  minQty : BitVec 32
  tif : Tif
  capacity : Capacity
  auctionType : AuctionType
  auctionId : BitVec 32
  disclosureMask : BitVec 8
  priceProtection : PriceProtection
  displayQty : BitVec 16
  displayWhen : DisplayWhen
  displayMethod : DisplayMethod
  displayLowQty : BitVec 16
  displayHighQty : BitVec 16
  positionEffectMask : BitVec 16
  stockLegShortSale : StockLegShortSale
  stockLegMpid : Alpha 4
  stockCapacity : StockCapacity
  sessionEligibility : SessionEligibility
  reserved8 : Alpha 8
  flexLegs : Bounded 1 FlexLegs
  deriving DecidableEq, Repr

namespace OrderAcceptedLongFormMessage

def encode (message : OrderAcceptedLongFormMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (encodeUInt 4 message.cmta
    ++ (Alpha.encode message.clearingAccount
    ++ (encodeUInt 4 message.occAccount
    ++ (Alpha.encode message.custAcct
    ++ (Alpha.encode message.preferredParty
    ++ (AloInst.encode message.aloInst
    ++ (Iso.encode message.iso
    ++ (Side.encode message.side
    ++ (OrderType.encode message.orderType
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.minQty
    ++ (Tif.encode message.tif
    ++ (Capacity.encode message.capacity
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 1 message.disclosureMask
    ++ (PriceProtection.encode message.priceProtection
    ++ (encodeUInt 2 message.displayQty
    ++ (DisplayWhen.encode message.displayWhen
    ++ (DisplayMethod.encode message.displayMethod
    ++ (encodeUInt 2 message.displayLowQty
    ++ (encodeUInt 2 message.displayHighQty
    ++ (encodeUInt 2 message.positionEffectMask
    ++ (StockLegShortSale.encode message.stockLegShortSale
    ++ (Alpha.encode message.stockLegMpid
    ++ (StockCapacity.encode message.stockCapacity
    ++ (SessionEligibility.encode message.sessionEligibility
    ++ (Alpha.encode message.reserved8
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.flexLegs.val.length)
    ++ (encodeMany FlexLegs.encode message.flexLegs.val)))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderAcceptedLongFormMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  let (cmta, bytes) ← decodeUInt 4 bytes
  let (clearingAccount, bytes) ← Alpha.decode 4 bytes
  let (occAccount, bytes) ← decodeUInt 4 bytes
  let (custAcct, bytes) ← Alpha.decode 10 bytes
  let (preferredParty, bytes) ← Alpha.decode 3 bytes
  let (aloInst, bytes) ← AloInst.decode bytes
  let (iso_, bytes) ← Iso.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (minQty, bytes) ← decodeUInt 4 bytes
  let (tif, bytes) ← Tif.decode bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (disclosureMask, bytes) ← decodeUInt 1 bytes
  let (priceProtection, bytes) ← PriceProtection.decode bytes
  let (displayQty, bytes) ← decodeUInt 2 bytes
  let (displayWhen, bytes) ← DisplayWhen.decode bytes
  let (displayMethod, bytes) ← DisplayMethod.decode bytes
  let (displayLowQty, bytes) ← decodeUInt 2 bytes
  let (displayHighQty, bytes) ← decodeUInt 2 bytes
  let (positionEffectMask, bytes) ← decodeUInt 2 bytes
  let (stockLegShortSale, bytes) ← StockLegShortSale.decode bytes
  let (stockLegMpid, bytes) ← Alpha.decode 4 bytes
  let (stockCapacity, bytes) ← StockCapacity.decode bytes
  let (sessionEligibility, bytes) ← SessionEligibility.decode bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (numberOfFlexLegs, bytes) ← decodeUInt 1 bytes
  let (flexLegs_, bytes) ← decodeMany FlexLegs.decode numberOfFlexLegs.toNat bytes
  if fits_flexLegs : flexLegs_.length < 256 ^ 1 then
    pure ({ timestamp, firmId, instrumentId, orderId, clOrdId, cmta, clearingAccount, occAccount, custAcct, preferredParty, aloInst, iso := iso_, side, orderType, price, quantity, minQty, tif, capacity, auctionType, auctionId, disclosureMask, priceProtection, displayQty, displayWhen, displayMethod, displayLowQty, displayHighQty, positionEffectMask, stockLegShortSale, stockLegMpid, stockCapacity, sessionEligibility, reserved8, flexLegs := ⟨flexLegs_, fits_flexLegs⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderAcceptedLongFormMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderAcceptedLongFormMessage) : (encode message).length ≤ 2160 := by
  have bound_flexLegs := message.flexLegs.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, AloInst.encode_length, Iso.encode_length, Side.encode_length, OrderType.encode_length, Tif.encode_length, Capacity.encode_length, AuctionType.encode_length, PriceProtection.encode_length, DisplayWhen.encode_length, DisplayMethod.encode_length, StockLegShortSale.encode_length, StockCapacity.encode_length, SessionEligibility.encode_length, encodeMany_length_const FlexLegs.encode 8 FlexLegs.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderAcceptedLongFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AloInst.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Iso.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Tif.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PriceProtection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, DisplayWhen.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DisplayMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StockLegShortSale.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StockCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SessionEligibility.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 FlexLegs.encode FlexLegs.decode FlexLegs.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.flexLegs.length_lt]
  rfl

end OrderAcceptedLongFormMessage

/-- Order Accepted Short Form Message: 65 bytes -/
structure OrderAcceptedShortFormMessage where
  timestamp : BitVec 64
  firmId : Alpha 4
  instrumentId : BitVec 32
  orderId : BitVec 64
  clOrdId : Alpha 16
  aloInst : AloInst
  iso : Iso
  side : Side
  orderType : OrderType
  price : BitVec 64
  quantityShort : BitVec 16
  tif : Tif
  capacity : Capacity
  auctionType : AuctionType
  auctionId : BitVec 32
  priceProtection : PriceProtection
  positionEffectMask : BitVec 16
  stockCapacity : StockCapacity
  deriving DecidableEq, Repr

namespace OrderAcceptedShortFormMessage

def encode (message : OrderAcceptedShortFormMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (AloInst.encode message.aloInst
    ++ (Iso.encode message.iso
    ++ (Side.encode message.side
    ++ (OrderType.encode message.orderType
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 2 message.quantityShort
    ++ (Tif.encode message.tif
    ++ (Capacity.encode message.capacity
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.auctionId
    ++ (PriceProtection.encode message.priceProtection
    ++ (encodeUInt 2 message.positionEffectMask
    ++ (StockCapacity.encode message.stockCapacity)))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAcceptedShortFormMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  let (aloInst, bytes) ← AloInst.decode bytes
  let (iso_, bytes) ← Iso.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (quantityShort, bytes) ← decodeUInt 2 bytes
  let (tif, bytes) ← Tif.decode bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (priceProtection, bytes) ← PriceProtection.decode bytes
  let (positionEffectMask, bytes) ← decodeUInt 2 bytes
  let (stockCapacity, bytes) ← StockCapacity.decode bytes
  pure ({ timestamp, firmId, instrumentId, orderId, clOrdId, aloInst, iso := iso_, side, orderType, price, quantityShort, tif, capacity, auctionType, auctionId, priceProtection, positionEffectMask, stockCapacity }, bytes)

@[simp] theorem encode_length (message : OrderAcceptedShortFormMessage) : (encode message).length = 65 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, AloInst.encode_length, Iso.encode_length, Side.encode_length, OrderType.encode_length, Tif.encode_length, Capacity.encode_length, AuctionType.encode_length, PriceProtection.encode_length, StockCapacity.encode_length]

theorem encode_length_pos (message : OrderAcceptedShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAcceptedShortFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AloInst.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Iso.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Tif.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PriceProtection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [StockCapacity.decode_encode, some_bind]
  rfl

end OrderAcceptedShortFormMessage

/-- Order Replaced Message: 100 bytes -/
structure OrderReplacedMessage where
  timestamp : BitVec 64
  firmId : Alpha 4
  instrumentId : BitVec 32
  origOrderId : BitVec 64
  orderId : BitVec 64
  origClOrdId : Alpha 16
  clOrdId : Alpha 16
  aloInst : AloInst
  iso : Iso
  side : Side
  orderType : OrderType
  price : BitVec 64
  quantity : BitVec 32
  tif : Tif
  custAcct : Alpha 10
  capacity : Capacity
  auctionType : AuctionType
  auctionId : BitVec 32
  positionEffectMask : BitVec 16
  priceProtection : PriceProtection
  deriving DecidableEq, Repr

namespace OrderReplacedMessage

def encode (message : OrderReplacedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.origOrderId
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.origClOrdId
    ++ (Alpha.encode message.clOrdId
    ++ (AloInst.encode message.aloInst
    ++ (Iso.encode message.iso
    ++ (Side.encode message.side
    ++ (OrderType.encode message.orderType
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.quantity
    ++ (Tif.encode message.tif
    ++ (Alpha.encode message.custAcct
    ++ (Capacity.encode message.capacity
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 2 message.positionEffectMask
    ++ (PriceProtection.encode message.priceProtection)))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderReplacedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (origOrderId, bytes) ← decodeUInt 8 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (origClOrdId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  let (aloInst, bytes) ← AloInst.decode bytes
  let (iso_, bytes) ← Iso.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (tif, bytes) ← Tif.decode bytes
  let (custAcct, bytes) ← Alpha.decode 10 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (positionEffectMask, bytes) ← decodeUInt 2 bytes
  let (priceProtection, bytes) ← PriceProtection.decode bytes
  pure ({ timestamp, firmId, instrumentId, origOrderId, orderId, origClOrdId, clOrdId, aloInst, iso := iso_, side, orderType, price, quantity, tif, custAcct, capacity, auctionType, auctionId, positionEffectMask, priceProtection }, bytes)

@[simp] theorem encode_length (message : OrderReplacedMessage) : (encode message).length = 100 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, AloInst.encode_length, Iso.encode_length, Side.encode_length, OrderType.encode_length, Tif.encode_length, Capacity.encode_length, AuctionType.encode_length, PriceProtection.encode_length]

theorem encode_length_pos (message : OrderReplacedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AloInst.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Iso.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Tif.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [PriceProtection.decode_encode, some_bind]
  rfl

end OrderReplacedMessage

/-- Order Canceled Message: 41 bytes -/
structure OrderCanceledMessage where
  timestamp : BitVec 64
  firmId : Alpha 4
  instrumentId : BitVec 32
  orderId : BitVec 64
  clOrdId : Alpha 16
  cancelReason : CancelReason
  deriving DecidableEq, Repr

namespace OrderCanceledMessage

def encode (message : OrderCanceledMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (CancelReason.encode message.cancelReason)))))

def decode (bytes : List UInt8) : Option (OrderCanceledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  let (cancelReason, bytes) ← CancelReason.decode bytes
  pure ({ timestamp, firmId, instrumentId, orderId, clOrdId, cancelReason }, bytes)

@[simp] theorem encode_length (message : OrderCanceledMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, CancelReason.encode_length]

theorem encode_length_pos (message : OrderCanceledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCanceledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [CancelReason.decode_encode, some_bind]
  rfl

end OrderCanceledMessage

/-- Order Executed Message: 72 bytes -/
structure OrderExecutedMessage where
  timestamp : BitVec 64
  firmId : Alpha 4
  productId : BitVec 16
  ordExecType : OrdExecType
  instrumentId : BitVec 32
  legInstrumentId : BitVec 32
  legId : BitVec 8
  auctionType : AuctionType
  orderId : BitVec 64
  clOrdId : Alpha 16
  crossId : BitVec 32
  matchId : BitVec 32
  side : Side
  stockLegShortSale : StockLegShortSale
  price : BitVec 64
  quantity : BitVec 32
  liquidityInd : BitVec 8
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 2 message.productId
    ++ (OrdExecType.encode message.ordExecType
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.legInstrumentId
    ++ (encodeUInt 1 message.legId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (encodeUInt 4 message.crossId
    ++ (encodeUInt 4 message.matchId
    ++ (Side.encode message.side
    ++ (StockLegShortSale.encode message.stockLegShortSale
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 1 message.liquidityInd))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (productId, bytes) ← decodeUInt 2 bytes
  let (ordExecType, bytes) ← OrdExecType.decode bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (legInstrumentId, bytes) ← decodeUInt 4 bytes
  let (legId, bytes) ← decodeUInt 1 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (stockLegShortSale, bytes) ← StockLegShortSale.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (liquidityInd, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, firmId, productId, ordExecType, instrumentId, legInstrumentId, legId, auctionType, orderId, clOrdId, crossId, matchId, side, stockLegShortSale, price, quantity, liquidityInd }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrdExecType.encode_length, AuctionType.encode_length, Side.encode_length, StockLegShortSale.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdExecType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StockLegShortSale.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedMessage

/-- Trade Details Message: 107 bytes -/
structure TradeDetailsMessage where
  timestamp : BitVec 64
  firmId : Alpha 4
  productId : BitVec 16
  ordExecType : OrdExecType
  instrumentId : BitVec 32
  legInstrumentId : BitVec 32
  legId : BitVec 8
  transType : TransType
  eventSource : EventSource
  auctionType : AuctionType
  orderId : BitVec 64
  clOrdId : Alpha 16
  crossId : BitVec 32
  matchId : BitVec 32
  refMatchId : BitVec 32
  side : Side
  stockLegShortSale : StockLegShortSale
  price : BitVec 64
  quantity : BitVec 32
  liquidityInd : BitVec 8
  cmta : BitVec 32
  clearingAccount : Alpha 4
  occAccount : BitVec 32
  custAcct : Alpha 10
  stockVenue : StockVenue
  stockLegMpid : Alpha 4
  capacity : Capacity
  openClose : OpenClose
  deriving DecidableEq, Repr

namespace TradeDetailsMessage

def encode (message : TradeDetailsMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 2 message.productId
    ++ (OrdExecType.encode message.ordExecType
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.legInstrumentId
    ++ (encodeUInt 1 message.legId
    ++ (TransType.encode message.transType
    ++ (EventSource.encode message.eventSource
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (encodeUInt 4 message.crossId
    ++ (encodeUInt 4 message.matchId
    ++ (encodeUInt 4 message.refMatchId
    ++ (Side.encode message.side
    ++ (StockLegShortSale.encode message.stockLegShortSale
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 1 message.liquidityInd
    ++ (encodeUInt 4 message.cmta
    ++ (Alpha.encode message.clearingAccount
    ++ (encodeUInt 4 message.occAccount
    ++ (Alpha.encode message.custAcct
    ++ (StockVenue.encode message.stockVenue
    ++ (Alpha.encode message.stockLegMpid
    ++ (Capacity.encode message.capacity
    ++ (OpenClose.encode message.openClose)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeDetailsMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (productId, bytes) ← decodeUInt 2 bytes
  let (ordExecType, bytes) ← OrdExecType.decode bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (legInstrumentId, bytes) ← decodeUInt 4 bytes
  let (legId, bytes) ← decodeUInt 1 bytes
  let (transType, bytes) ← TransType.decode bytes
  let (eventSource, bytes) ← EventSource.decode bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  let (refMatchId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (stockLegShortSale, bytes) ← StockLegShortSale.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (liquidityInd, bytes) ← decodeUInt 1 bytes
  let (cmta, bytes) ← decodeUInt 4 bytes
  let (clearingAccount, bytes) ← Alpha.decode 4 bytes
  let (occAccount, bytes) ← decodeUInt 4 bytes
  let (custAcct, bytes) ← Alpha.decode 10 bytes
  let (stockVenue, bytes) ← StockVenue.decode bytes
  let (stockLegMpid, bytes) ← Alpha.decode 4 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  pure ({ timestamp, firmId, productId, ordExecType, instrumentId, legInstrumentId, legId, transType, eventSource, auctionType, orderId, clOrdId, crossId, matchId, refMatchId, side, stockLegShortSale, price, quantity, liquidityInd, cmta, clearingAccount, occAccount, custAcct, stockVenue, stockLegMpid, capacity, openClose }, bytes)

@[simp] theorem encode_length (message : TradeDetailsMessage) : (encode message).length = 107 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrdExecType.encode_length, TransType.encode_length, EventSource.encode_length, AuctionType.encode_length, Side.encode_length, StockLegShortSale.encode_length, StockVenue.encode_length, Capacity.encode_length, OpenClose.encode_length]

theorem encode_length_pos (message : TradeDetailsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeDetailsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TransType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventSource.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StockLegShortSale.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StockVenue.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [OpenClose.decode_encode, some_bind]
  rfl

end TradeDetailsMessage

/-- Cross Order Accepted Message: 169 bytes -/
structure CrossOrderAcceptedMessage where
  timestamp : BitVec 64
  firmId : Alpha 4
  instrumentId : BitVec 32
  crossType : CrossType
  auctionType : AuctionType
  auctionId : BitVec 32
  auctionAllocPct : BitVec 8
  side : Side
  iso : Iso
  priceProtection : PriceProtection
  effectiveTime : BitVec 64
  disclosureMask : BitVec 8
  primaryOrderId : BitVec 64
  primaryClOrdId : Alpha 16
  primaryCmta : BitVec 32
  primaryClearingAccount : Alpha 4
  primaryOccAccount : BitVec 32
  primaryCustAcct : Alpha 10
  primaryPrice : BitVec 64
  primaryQuantity : BitVec 32
  primaryCapacity : PrimaryCapacity
  primaryPositionEffectMask : BitVec 16
  primaryStockLegShortSale : PrimaryStockLegShortSale
  primaryStockLegMpid : Alpha 4
  contraOrderId : BitVec 64
  contraClOrdId : Alpha 16
  contraCmta : BitVec 32
  contraClearingAccount : Alpha 4
  contraOccAccount : BitVec 32
  contraCustAcct : Alpha 10
  contraOrderType : ContraOrderType
  contraPrice : BitVec 64
  contraQuantity : BitVec 32
  contraCapacity : ContraCapacity
  contraPositionEffectMask : BitVec 16
  contraStockLegShortSale : ContraStockLegShortSale
  contraStockLegMpid : Alpha 4
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace CrossOrderAcceptedMessage

def encode (message : CrossOrderAcceptedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 4 message.instrumentId
    ++ (CrossType.encode message.crossType
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 1 message.auctionAllocPct
    ++ (Side.encode message.side
    ++ (Iso.encode message.iso
    ++ (PriceProtection.encode message.priceProtection
    ++ (encodeUInt 8 message.effectiveTime
    ++ (encodeUInt 1 message.disclosureMask
    ++ (encodeUInt 8 message.primaryOrderId
    ++ (Alpha.encode message.primaryClOrdId
    ++ (encodeUInt 4 message.primaryCmta
    ++ (Alpha.encode message.primaryClearingAccount
    ++ (encodeUInt 4 message.primaryOccAccount
    ++ (Alpha.encode message.primaryCustAcct
    ++ (encodeUInt 8 message.primaryPrice
    ++ (encodeUInt 4 message.primaryQuantity
    ++ (PrimaryCapacity.encode message.primaryCapacity
    ++ (encodeUInt 2 message.primaryPositionEffectMask
    ++ (PrimaryStockLegShortSale.encode message.primaryStockLegShortSale
    ++ (Alpha.encode message.primaryStockLegMpid
    ++ (encodeUInt 8 message.contraOrderId
    ++ (Alpha.encode message.contraClOrdId
    ++ (encodeUInt 4 message.contraCmta
    ++ (Alpha.encode message.contraClearingAccount
    ++ (encodeUInt 4 message.contraOccAccount
    ++ (Alpha.encode message.contraCustAcct
    ++ (ContraOrderType.encode message.contraOrderType
    ++ (encodeUInt 8 message.contraPrice
    ++ (encodeUInt 4 message.contraQuantity
    ++ (ContraCapacity.encode message.contraCapacity
    ++ (encodeUInt 2 message.contraPositionEffectMask
    ++ (ContraStockLegShortSale.encode message.contraStockLegShortSale
    ++ (Alpha.encode message.contraStockLegMpid
    ++ (Alpha.encode message.reserved1)))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (CrossOrderAcceptedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (auctionAllocPct, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← Side.decode bytes
  let (iso_, bytes) ← Iso.decode bytes
  let (priceProtection, bytes) ← PriceProtection.decode bytes
  let (effectiveTime, bytes) ← decodeUInt 8 bytes
  let (disclosureMask, bytes) ← decodeUInt 1 bytes
  let (primaryOrderId, bytes) ← decodeUInt 8 bytes
  let (primaryClOrdId, bytes) ← Alpha.decode 16 bytes
  let (primaryCmta, bytes) ← decodeUInt 4 bytes
  let (primaryClearingAccount, bytes) ← Alpha.decode 4 bytes
  let (primaryOccAccount, bytes) ← decodeUInt 4 bytes
  let (primaryCustAcct, bytes) ← Alpha.decode 10 bytes
  let (primaryPrice, bytes) ← decodeUInt 8 bytes
  let (primaryQuantity, bytes) ← decodeUInt 4 bytes
  let (primaryCapacity, bytes) ← PrimaryCapacity.decode bytes
  let (primaryPositionEffectMask, bytes) ← decodeUInt 2 bytes
  let (primaryStockLegShortSale, bytes) ← PrimaryStockLegShortSale.decode bytes
  let (primaryStockLegMpid, bytes) ← Alpha.decode 4 bytes
  let (contraOrderId, bytes) ← decodeUInt 8 bytes
  let (contraClOrdId, bytes) ← Alpha.decode 16 bytes
  let (contraCmta, bytes) ← decodeUInt 4 bytes
  let (contraClearingAccount, bytes) ← Alpha.decode 4 bytes
  let (contraOccAccount, bytes) ← decodeUInt 4 bytes
  let (contraCustAcct, bytes) ← Alpha.decode 10 bytes
  let (contraOrderType, bytes) ← ContraOrderType.decode bytes
  let (contraPrice, bytes) ← decodeUInt 8 bytes
  let (contraQuantity, bytes) ← decodeUInt 4 bytes
  let (contraCapacity, bytes) ← ContraCapacity.decode bytes
  let (contraPositionEffectMask, bytes) ← decodeUInt 2 bytes
  let (contraStockLegShortSale, bytes) ← ContraStockLegShortSale.decode bytes
  let (contraStockLegMpid, bytes) ← Alpha.decode 4 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ timestamp, firmId, instrumentId, crossType, auctionType, auctionId, auctionAllocPct, side, iso := iso_, priceProtection, effectiveTime, disclosureMask, primaryOrderId, primaryClOrdId, primaryCmta, primaryClearingAccount, primaryOccAccount, primaryCustAcct, primaryPrice, primaryQuantity, primaryCapacity, primaryPositionEffectMask, primaryStockLegShortSale, primaryStockLegMpid, contraOrderId, contraClOrdId, contraCmta, contraClearingAccount, contraOccAccount, contraCustAcct, contraOrderType, contraPrice, contraQuantity, contraCapacity, contraPositionEffectMask, contraStockLegShortSale, contraStockLegMpid, reserved1 }, bytes)

@[simp] theorem encode_length (message : CrossOrderAcceptedMessage) : (encode message).length = 169 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, CrossType.encode_length, AuctionType.encode_length, Side.encode_length, Iso.encode_length, PriceProtection.encode_length, PrimaryCapacity.encode_length, PrimaryStockLegShortSale.encode_length, ContraOrderType.encode_length, ContraCapacity.encode_length, ContraStockLegShortSale.encode_length]

theorem encode_length_pos (message : CrossOrderAcceptedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : CrossOrderAcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Iso.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceProtection.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryStockLegShortSale.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContraOrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContraCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContraStockLegShortSale.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CrossOrderAcceptedMessage

/-- Member Kill Switch Notification Message: 33 bytes -/
structure MemberKillSwitchNotificationMessage where
  timestamp : BitVec 64
  firmId : Alpha 4
  clRequestId : Alpha 16
  targetFirmId : Alpha 4
  killAction : KillAction
  deriving DecidableEq, Repr

namespace MemberKillSwitchNotificationMessage

def encode (message : MemberKillSwitchNotificationMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.firmId
    ++ (Alpha.encode message.clRequestId
    ++ (Alpha.encode message.targetFirmId
    ++ (KillAction.encode message.killAction))))

def decode (bytes : List UInt8) : Option (MemberKillSwitchNotificationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (clRequestId, bytes) ← Alpha.decode 16 bytes
  let (targetFirmId, bytes) ← Alpha.decode 4 bytes
  let (killAction, bytes) ← KillAction.decode bytes
  pure ({ timestamp, firmId, clRequestId, targetFirmId, killAction }, bytes)

@[simp] theorem encode_length (message : MemberKillSwitchNotificationMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, KillAction.encode_length]

theorem encode_length_pos (message : MemberKillSwitchNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MemberKillSwitchNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [KillAction.decode_encode, some_bind]
  rfl

end MemberKillSwitchNotificationMessage

/-- Mass Cancel Response Message: 36 bytes -/
structure MassCancelResponseMessage where
  timestamp : BitVec 64
  firmId : Alpha 4
  clRequestId : Alpha 16
  numCanceled : BitVec 32
  numPending : BitVec 32
  deriving DecidableEq, Repr

namespace MassCancelResponseMessage

def encode (message : MassCancelResponseMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.firmId
    ++ (Alpha.encode message.clRequestId
    ++ (encodeUInt 4 message.numCanceled
    ++ (encodeUInt 4 message.numPending))))

def decode (bytes : List UInt8) : Option (MassCancelResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (clRequestId, bytes) ← Alpha.decode 16 bytes
  let (numCanceled, bytes) ← decodeUInt 4 bytes
  let (numPending, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, firmId, clRequestId, numCanceled, numPending }, bytes)

@[simp] theorem encode_length (message : MassCancelResponseMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MassCancelResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassCancelResponseMessage

/-- Add Complex Instrument Response Message: 32 bytes -/
structure AddComplexInstrumentResponseMessage where
  timestamp : BitVec 64
  firmId : Alpha 4
  clRequestId : Alpha 16
  instrumentId : BitVec 32
  deriving DecidableEq, Repr

namespace AddComplexInstrumentResponseMessage

def encode (message : AddComplexInstrumentResponseMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.firmId
    ++ (Alpha.encode message.clRequestId
    ++ (encodeUInt 4 message.instrumentId)))

def decode (bytes : List UInt8) : Option (AddComplexInstrumentResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (clRequestId, bytes) ← Alpha.decode 16 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, firmId, clRequestId, instrumentId }, bytes)

@[simp] theorem encode_length (message : AddComplexInstrumentResponseMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : AddComplexInstrumentResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddComplexInstrumentResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddComplexInstrumentResponseMessage

/-- Modify Trade Response Message: 56 bytes -/
structure ModifyTradeResponseMessage where
  timestamp : BitVec 64
  firmId : Alpha 4
  instrumentId : BitVec 32
  clRequestId : Alpha 16
  clOrdId : Alpha 16
  crossId : BitVec 32
  matchId : BitVec 32
  deriving DecidableEq, Repr

namespace ModifyTradeResponseMessage

def encode (message : ModifyTradeResponseMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 4 message.instrumentId
    ++ (Alpha.encode message.clRequestId
    ++ (Alpha.encode message.clOrdId
    ++ (encodeUInt 4 message.crossId
    ++ (encodeUInt 4 message.matchId))))))

def decode (bytes : List UInt8) : Option (ModifyTradeResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (clRequestId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, firmId, instrumentId, clRequestId, clOrdId, crossId, matchId }, bytes)

@[simp] theorem encode_length (message : ModifyTradeResponseMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ModifyTradeResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyTradeResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ModifyTradeResponseMessage

/-- Subscription Response Message: 28 bytes -/
structure SubscriptionResponseMessage where
  timestamp : BitVec 64
  firmId : Alpha 4
  clRequestId : Alpha 16
  deriving DecidableEq, Repr

namespace SubscriptionResponseMessage

def encode (message : SubscriptionResponseMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.firmId
    ++ (Alpha.encode message.clRequestId))

def decode (bytes : List UInt8) : Option (SubscriptionResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (clRequestId, bytes) ← Alpha.decode 16 bytes
  pure ({ timestamp, firmId, clRequestId }, bytes)

@[simp] theorem encode_length (message : SubscriptionResponseMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SubscriptionResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SubscriptionResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SubscriptionResponseMessage

/-- Reject Message: 27 bytes -/
structure RejectMessage where
  timestamp : BitVec 64
  rejectMsgType : Alpha 1
  clOrdId : Alpha 16
  rejectCode : BitVec 16
  deriving DecidableEq, Repr

namespace RejectMessage

def encode (message : RejectMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.rejectMsgType
    ++ (Alpha.encode message.clOrdId
    ++ (encodeUInt 2 message.rejectCode)))

def decode (bytes : List UInt8) : Option (RejectMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (rejectMsgType, bytes) ← Alpha.decode 1 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  let (rejectCode, bytes) ← decodeUInt 2 bytes
  pure ({ timestamp, rejectMsgType, clOrdId, rejectCode }, bytes)

@[simp] theorem encode_length (message : RejectMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RejectMessage

/-- Pending Response Message: 34 bytes -/
structure PendingResponseMessage where
  timestamp : BitVec 64
  firmId : Alpha 4
  instrumentId : BitVec 32
  pendingMsgType : Alpha 1
  clOrdId : Alpha 16
  pendingReason : PendingReason
  deriving DecidableEq, Repr

namespace PendingResponseMessage

def encode (message : PendingResponseMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 4 message.instrumentId
    ++ (Alpha.encode message.pendingMsgType
    ++ (Alpha.encode message.clOrdId
    ++ (PendingReason.encode message.pendingReason)))))

def decode (bytes : List UInt8) : Option (PendingResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (pendingMsgType, bytes) ← Alpha.decode 1 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  let (pendingReason, bytes) ← PendingReason.decode bytes
  pure ({ timestamp, firmId, instrumentId, pendingMsgType, clOrdId, pendingReason }, bytes)

@[simp] theorem encode_length (message : PendingResponseMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, PendingReason.encode_length]

theorem encode_length_pos (message : PendingResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PendingResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PendingReason.decode_encode, some_bind]
  rfl

end PendingResponseMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- "z" 0x7A
  | simpleInstrumentDirectoryMessage (message : SimpleInstrumentDirectoryMessage) -- "o" 0x6F
  | complexInstrumentDirectoryMessage (message : ComplexInstrumentDirectoryMessage) -- "s" 0x73
  | instrumentTradingActionMessage (message : InstrumentTradingActionMessage) -- "i" 0x69
  | auctionNotificationMessage (message : AuctionNotificationMessage) -- "n" 0x6E
  | orderAcceptedLongFormMessage (message : OrderAcceptedLongFormMessage) -- "a" 0x61
  | orderAcceptedShortFormMessage (message : OrderAcceptedShortFormMessage) -- "b" 0x62
  | orderReplacedMessage (message : OrderReplacedMessage) -- "r" 0x72
  | orderCanceledMessage (message : OrderCanceledMessage) -- "c" 0x63
  | orderExecutedMessage (message : OrderExecutedMessage) -- "e" 0x65
  | tradeDetailsMessage (message : TradeDetailsMessage) -- "t" 0x74
  | crossOrderAcceptedMessage (message : CrossOrderAcceptedMessage) -- "x" 0x78
  | memberKillSwitchNotificationMessage (message : MemberKillSwitchNotificationMessage) -- "k" 0x6B
  | massCancelResponseMessage (message : MassCancelResponseMessage) -- "u" 0x75
  | addComplexInstrumentResponseMessage (message : AddComplexInstrumentResponseMessage) -- "d" 0x64
  | modifyTradeResponseMessage (message : ModifyTradeResponseMessage) -- "m" 0x6D
  | subscriptionResponseMessage (message : SubscriptionResponseMessage) -- "f" 0x66
  | rejectMessage (message : RejectMessage) -- "j" 0x6A
  | pendingResponseMessage (message : PendingResponseMessage) -- "p" 0x70
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 122
  | .simpleInstrumentDirectoryMessage _ => 111
  | .complexInstrumentDirectoryMessage _ => 115
  | .instrumentTradingActionMessage _ => 105
  | .auctionNotificationMessage _ => 110
  | .orderAcceptedLongFormMessage _ => 97
  | .orderAcceptedShortFormMessage _ => 98
  | .orderReplacedMessage _ => 114
  | .orderCanceledMessage _ => 99
  | .orderExecutedMessage _ => 101
  | .tradeDetailsMessage _ => 116
  | .crossOrderAcceptedMessage _ => 120
  | .memberKillSwitchNotificationMessage _ => 107
  | .massCancelResponseMessage _ => 117
  | .addComplexInstrumentResponseMessage _ => 100
  | .modifyTradeResponseMessage _ => 109
  | .subscriptionResponseMessage _ => 102
  | .rejectMessage _ => 106
  | .pendingResponseMessage _ => 112

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .simpleInstrumentDirectoryMessage message => SimpleInstrumentDirectoryMessage.encode message
  | .complexInstrumentDirectoryMessage message => ComplexInstrumentDirectoryMessage.encode message
  | .instrumentTradingActionMessage message => InstrumentTradingActionMessage.encode message
  | .auctionNotificationMessage message => AuctionNotificationMessage.encode message
  | .orderAcceptedLongFormMessage message => OrderAcceptedLongFormMessage.encode message
  | .orderAcceptedShortFormMessage message => OrderAcceptedShortFormMessage.encode message
  | .orderReplacedMessage message => OrderReplacedMessage.encode message
  | .orderCanceledMessage message => OrderCanceledMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .tradeDetailsMessage message => TradeDetailsMessage.encode message
  | .crossOrderAcceptedMessage message => CrossOrderAcceptedMessage.encode message
  | .memberKillSwitchNotificationMessage message => MemberKillSwitchNotificationMessage.encode message
  | .massCancelResponseMessage message => MassCancelResponseMessage.encode message
  | .addComplexInstrumentResponseMessage message => AddComplexInstrumentResponseMessage.encode message
  | .modifyTradeResponseMessage message => ModifyTradeResponseMessage.encode message
  | .subscriptionResponseMessage message => SubscriptionResponseMessage.encode message
  | .rejectMessage message => RejectMessage.encode message
  | .pendingResponseMessage message => PendingResponseMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 2324 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | simpleInstrumentDirectoryMessage inner =>
    simp only [encode, SimpleInstrumentDirectoryMessage.encode_length]
    omega
  | complexInstrumentDirectoryMessage inner =>
    have bound_inner := ComplexInstrumentDirectoryMessage.encode_length_le inner
    simp only [encode]
    omega
  | instrumentTradingActionMessage inner =>
    simp only [encode, InstrumentTradingActionMessage.encode_length]
    omega
  | auctionNotificationMessage inner =>
    have bound_inner := AuctionNotificationMessage.encode_length_le inner
    simp only [encode]
    omega
  | orderAcceptedLongFormMessage inner =>
    have bound_inner := OrderAcceptedLongFormMessage.encode_length_le inner
    simp only [encode]
    omega
  | orderAcceptedShortFormMessage inner =>
    simp only [encode, OrderAcceptedShortFormMessage.encode_length]
    omega
  | orderReplacedMessage inner =>
    simp only [encode, OrderReplacedMessage.encode_length]
    omega
  | orderCanceledMessage inner =>
    simp only [encode, OrderCanceledMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | tradeDetailsMessage inner =>
    simp only [encode, TradeDetailsMessage.encode_length]
    omega
  | crossOrderAcceptedMessage inner =>
    simp only [encode, CrossOrderAcceptedMessage.encode_length]
    omega
  | memberKillSwitchNotificationMessage inner =>
    simp only [encode, MemberKillSwitchNotificationMessage.encode_length]
    omega
  | massCancelResponseMessage inner =>
    simp only [encode, MassCancelResponseMessage.encode_length]
    omega
  | addComplexInstrumentResponseMessage inner =>
    simp only [encode, AddComplexInstrumentResponseMessage.encode_length]
    omega
  | modifyTradeResponseMessage inner =>
    simp only [encode, ModifyTradeResponseMessage.encode_length]
    omega
  | subscriptionResponseMessage inner =>
    simp only [encode, SubscriptionResponseMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [encode, RejectMessage.encode_length]
    omega
  | pendingResponseMessage inner =>
    simp only [encode, PendingResponseMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 122 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 111 then (SimpleInstrumentDirectoryMessage.decode bytes).map fun (message, rest) => (.simpleInstrumentDirectoryMessage message, rest)
  else if tag = 115 then (ComplexInstrumentDirectoryMessage.decode bytes).map fun (message, rest) => (.complexInstrumentDirectoryMessage message, rest)
  else if tag = 105 then (InstrumentTradingActionMessage.decode bytes).map fun (message, rest) => (.instrumentTradingActionMessage message, rest)
  else if tag = 110 then (AuctionNotificationMessage.decode bytes).map fun (message, rest) => (.auctionNotificationMessage message, rest)
  else if tag = 97 then (OrderAcceptedLongFormMessage.decode bytes).map fun (message, rest) => (.orderAcceptedLongFormMessage message, rest)
  else if tag = 98 then (OrderAcceptedShortFormMessage.decode bytes).map fun (message, rest) => (.orderAcceptedShortFormMessage message, rest)
  else if tag = 114 then (OrderReplacedMessage.decode bytes).map fun (message, rest) => (.orderReplacedMessage message, rest)
  else if tag = 99 then (OrderCanceledMessage.decode bytes).map fun (message, rest) => (.orderCanceledMessage message, rest)
  else if tag = 101 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 116 then (TradeDetailsMessage.decode bytes).map fun (message, rest) => (.tradeDetailsMessage message, rest)
  else if tag = 120 then (CrossOrderAcceptedMessage.decode bytes).map fun (message, rest) => (.crossOrderAcceptedMessage message, rest)
  else if tag = 107 then (MemberKillSwitchNotificationMessage.decode bytes).map fun (message, rest) => (.memberKillSwitchNotificationMessage message, rest)
  else if tag = 117 then (MassCancelResponseMessage.decode bytes).map fun (message, rest) => (.massCancelResponseMessage message, rest)
  else if tag = 100 then (AddComplexInstrumentResponseMessage.decode bytes).map fun (message, rest) => (.addComplexInstrumentResponseMessage message, rest)
  else if tag = 109 then (ModifyTradeResponseMessage.decode bytes).map fun (message, rest) => (.modifyTradeResponseMessage message, rest)
  else if tag = 102 then (SubscriptionResponseMessage.decode bytes).map fun (message, rest) => (.subscriptionResponseMessage message, rest)
  else if tag = 106 then (RejectMessage.decode bytes).map fun (message, rest) => (.rejectMessage message, rest)
  else if tag = 112 then (PendingResponseMessage.decode bytes).map fun (message, rest) => (.pendingResponseMessage message, rest)
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
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 2325 := by
  unfold encode
  cases message.sequencedMessage with
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | simpleInstrumentDirectoryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SimpleInstrumentDirectoryMessage.encode_length]
    omega
  | complexInstrumentDirectoryMessage inner =>
    have bound_inner := ComplexInstrumentDirectoryMessage.encode_length_le inner
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | instrumentTradingActionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, InstrumentTradingActionMessage.encode_length]
    omega
  | auctionNotificationMessage inner =>
    have bound_inner := AuctionNotificationMessage.encode_length_le inner
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | orderAcceptedLongFormMessage inner =>
    have bound_inner := OrderAcceptedLongFormMessage.encode_length_le inner
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | orderAcceptedShortFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderAcceptedShortFormMessage.encode_length]
    omega
  | orderReplacedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderReplacedMessage.encode_length]
    omega
  | orderCanceledMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderCanceledMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | tradeDetailsMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TradeDetailsMessage.encode_length]
    omega
  | crossOrderAcceptedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, CrossOrderAcceptedMessage.encode_length]
    omega
  | memberKillSwitchNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, MemberKillSwitchNotificationMessage.encode_length]
    omega
  | massCancelResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, MassCancelResponseMessage.encode_length]
    omega
  | addComplexInstrumentResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddComplexInstrumentResponseMessage.encode_length]
    omega
  | modifyTradeResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ModifyTradeResponseMessage.encode_length]
    omega
  | subscriptionResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SubscriptionResponseMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, RejectMessage.encode_length]
    omega
  | pendingResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, PendingResponseMessage.encode_length]
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
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 2325 := by
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

end Omi.NasdaqUsoptionsOttoOuchV300Server
