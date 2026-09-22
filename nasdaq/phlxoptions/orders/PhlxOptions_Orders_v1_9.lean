import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) PHLX Orders v1.9

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: Expiration is a bit field set, proven as its 2 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqPhlxoptionsOrdersItchV19

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

/-- Option Closing Type: one byte code -/
def OptionClosingType.codes : List UInt8 :=
  [0x4E, 0x4C, 0x57]

inductive OptionClosingType where
  | normal -- Normal
  | late -- Late
  | wcoEarlyClosing -- Wco Early Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionClosingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionClosingType

def toByte : OptionClosingType → UInt8
  | .normal => 0x4E
  | .late => 0x4C
  | .wcoEarlyClosing => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionClosingType :=
  if byte = 0x4E then .normal
  else if byte = 0x4C then .late
  else .wcoEarlyClosing

def ofByte (byte : UInt8) : OptionClosingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionClosingType) : ofByte value.toByte = value := by
  cases value with
  | normal => decide
  | late => decide
  | wcoEarlyClosing => decide
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

/-- Phlx Tradable: one byte code -/
def PhlxTradable.codes : List UInt8 :=
  [0x59, 0x4E]

inductive PhlxTradable where
  | tradable -- Tradable
  | notTradable -- Not Tradable
  | unlisted (byte : { byte : UInt8 // byte ∉ PhlxTradable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PhlxTradable

def toByte : PhlxTradable → UInt8
  | .tradable => 0x59
  | .notTradable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PhlxTradable :=
  if byte = 0x59 then .tradable
  else .notTradable

def ofByte (byte : UInt8) : PhlxTradable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PhlxTradable) : ofByte value.toByte = value := by
  cases value with
  | tradable => decide
  | notTradable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PhlxTradable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PhlxTradable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PhlxTradable) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PhlxTradable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PhlxTradable

/-- Action: one byte code -/
def Action.codes : List UInt8 :=
  [0x41, 0x44]

inductive Action where
  | add -- Add
  | delete -- Delete
  | unlisted (byte : { byte : UInt8 // byte ∉ Action.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Action

def toByte : Action → UInt8
  | .add => 0x41
  | .delete => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Action :=
  if byte = 0x41 then .add
  else .delete

def ofByte (byte : UInt8) : Action :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Action) : ofByte value.toByte = value := by
  cases value with
  | add => decide
  | delete => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Action) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Action × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Action) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Action) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Action

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x2A]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | hidden -- Hidden
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .hidden => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .hidden

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
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

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x48, 0x54]

inductive CurrentTradingState where
  | haltInEffect -- Halt In Effect
  | phlxTradingResumed -- Phlx Trading Resumed
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .haltInEffect => 0x48
  | .phlxTradingResumed => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .haltInEffect
  else .phlxTradingResumed

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | haltInEffect => decide
  | phlxTradingResumed => decide
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

/-- Order Status: one byte code -/
def OrderStatus.codes : List UInt8 :=
  [0x4F, 0x46, 0x43, 0x52]

inductive OrderStatus where
  | open_ -- Open
  | filled -- Filled
  | cancelled -- Cancelled
  | renotification -- Renotification
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderStatus

def toByte : OrderStatus → UInt8
  | .open_ => 0x4F
  | .filled => 0x46
  | .cancelled => 0x43
  | .renotification => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderStatus :=
  if byte = 0x4F then .open_
  else if byte = 0x46 then .filled
  else if byte = 0x43 then .cancelled
  else .renotification

def ofByte (byte : UInt8) : OrderStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderStatus) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | filled => decide
  | cancelled => decide
  | renotification => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderStatus

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x4D, 0x4C, 0x2A]

inductive OrderType where
  | market -- Market
  | limit -- Limit
  | anonymous -- Anonymous
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .market => 0x4D
  | .limit => 0x4C
  | .anonymous => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x4D then .market
  else if byte = 0x4C then .limit
  else .anonymous

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | limit => decide
  | anonymous => decide
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

/-- Market Qualifier: one byte code -/
def MarketQualifier.codes : List UInt8 :=
  [0x4F, 0x49, 0x20]

inductive MarketQualifier where
  | openingOrder -- Opening Order
  | impliedOrder -- Implied Order
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketQualifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketQualifier

def toByte : MarketQualifier → UInt8
  | .openingOrder => 0x4F
  | .impliedOrder => 0x49
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketQualifier :=
  if byte = 0x4F then .openingOrder
  else if byte = 0x49 then .impliedOrder
  else .na

def ofByte (byte : UInt8) : MarketQualifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketQualifier) : ofByte value.toByte = value := by
  cases value with
  | openingOrder => decide
  | impliedOrder => decide
  | na => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketQualifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketQualifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketQualifier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketQualifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketQualifier

/-- All Or None: one byte code -/
def AllOrNone.codes : List UInt8 :=
  [0x59, 0x4E]

inductive AllOrNone where
  | allOrNoneOrder -- All Or None Order
  | notAllOrNoneOrder -- Not All Or None Order
  | unlisted (byte : { byte : UInt8 // byte ∉ AllOrNone.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AllOrNone

def toByte : AllOrNone → UInt8
  | .allOrNoneOrder => 0x59
  | .notAllOrNoneOrder => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AllOrNone :=
  if byte = 0x59 then .allOrNoneOrder
  else .notAllOrNoneOrder

def ofByte (byte : UInt8) : AllOrNone :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AllOrNone) : ofByte value.toByte = value := by
  cases value with
  | allOrNoneOrder => decide
  | notAllOrNoneOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AllOrNone) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AllOrNone × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AllOrNone) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AllOrNone) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AllOrNone

/-- Time In Force: one byte code -/
def TimeInForce.codes : List UInt8 :=
  [0x44, 0x47, 0x49]

inductive TimeInForce where
  | dayOrder -- Day Order
  | gtc -- Gtc
  | ioc -- Ioc
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForce

def toByte : TimeInForce → UInt8
  | .dayOrder => 0x44
  | .gtc => 0x47
  | .ioc => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForce :=
  if byte = 0x44 then .dayOrder
  else if byte = 0x47 then .gtc
  else .ioc

def ofByte (byte : UInt8) : TimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForce) : ofByte value.toByte = value := by
  cases value with
  | dayOrder => decide
  | gtc => decide
  | ioc => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForce) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForce × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForce) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TimeInForce) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForce

/-- Customer Firm Indicator: one byte code -/
def CustomerFirmIndicator.codes : List UInt8 :=
  [0x43, 0x46, 0x4D, 0x42, 0x50, 0x20]

inductive CustomerFirmIndicator where
  | customerOrder -- Customer Order
  | firmOrder -- Firm Order
  | onfloorMarketMaker -- Onfloor Market Maker
  | brokerDealerOrder -- Broker Dealer Order
  | professionalOrder -- Professional Order
  | naForImpliedOrder -- Na For Implied Order
  | unlisted (byte : { byte : UInt8 // byte ∉ CustomerFirmIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CustomerFirmIndicator

def toByte : CustomerFirmIndicator → UInt8
  | .customerOrder => 0x43
  | .firmOrder => 0x46
  | .onfloorMarketMaker => 0x4D
  | .brokerDealerOrder => 0x42
  | .professionalOrder => 0x50
  | .naForImpliedOrder => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CustomerFirmIndicator :=
  if byte = 0x43 then .customerOrder
  else if byte = 0x46 then .firmOrder
  else if byte = 0x4D then .onfloorMarketMaker
  else if byte = 0x42 then .brokerDealerOrder
  else if byte = 0x50 then .professionalOrder
  else .naForImpliedOrder

def ofByte (byte : UInt8) : CustomerFirmIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CustomerFirmIndicator) : ofByte value.toByte = value := by
  cases value with
  | customerOrder => decide
  | firmOrder => decide
  | onfloorMarketMaker => decide
  | brokerDealerOrder => decide
  | professionalOrder => decide
  | naForImpliedOrder => decide
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

/-- Open Close Indicator: one byte code -/
def OpenCloseIndicator.codes : List UInt8 :=
  [0x4F, 0x43, 0x20]

inductive OpenCloseIndicator where
  | opensPosition -- Opens Position
  | closesPosition -- Closes Position
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenCloseIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenCloseIndicator

def toByte : OpenCloseIndicator → UInt8
  | .opensPosition => 0x4F
  | .closesPosition => 0x43
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenCloseIndicator :=
  if byte = 0x4F then .opensPosition
  else if byte = 0x43 then .closesPosition
  else .na

def ofByte (byte : UInt8) : OpenCloseIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenCloseIndicator) : ofByte value.toByte = value := by
  cases value with
  | opensPosition => decide
  | closesPosition => decide
  | na => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenCloseIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenCloseIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenCloseIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenCloseIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenCloseIndicator

/-- Debit Or Credit: one byte code -/
def DebitOrCredit.codes : List UInt8 :=
  [0x44, 0x43, 0x20, 0x2A]

inductive DebitOrCredit where
  | netDebit -- Net Debit
  | netCredit -- Net Credit
  | evenOrMarketOrder -- Even Or Market Order
  | anonymous -- Anonymous
  | unlisted (byte : { byte : UInt8 // byte ∉ DebitOrCredit.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DebitOrCredit

def toByte : DebitOrCredit → UInt8
  | .netDebit => 0x44
  | .netCredit => 0x43
  | .evenOrMarketOrder => 0x20
  | .anonymous => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DebitOrCredit :=
  if byte = 0x44 then .netDebit
  else if byte = 0x43 then .netCredit
  else if byte = 0x20 then .evenOrMarketOrder
  else .anonymous

def ofByte (byte : UInt8) : DebitOrCredit :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DebitOrCredit) : ofByte value.toByte = value := by
  cases value with
  | netDebit => decide
  | netCredit => decide
  | evenOrMarketOrder => decide
  | anonymous => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DebitOrCredit) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DebitOrCredit × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DebitOrCredit) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DebitOrCredit) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DebitOrCredit

/-- Leg Open Close Indicator: one byte code -/
def LegOpenCloseIndicator.codes : List UInt8 :=
  [0x4F, 0x43, 0x20]

inductive LegOpenCloseIndicator where
  | opensPosition -- Opens Position
  | closesPosition -- Closes Position
  | stockLeg -- Stock Leg
  | unlisted (byte : { byte : UInt8 // byte ∉ LegOpenCloseIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegOpenCloseIndicator

def toByte : LegOpenCloseIndicator → UInt8
  | .opensPosition => 0x4F
  | .closesPosition => 0x43
  | .stockLeg => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegOpenCloseIndicator :=
  if byte = 0x4F then .opensPosition
  else if byte = 0x43 then .closesPosition
  else .stockLeg

def ofByte (byte : UInt8) : LegOpenCloseIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegOpenCloseIndicator) : ofByte value.toByte = value := by
  cases value with
  | opensPosition => decide
  | closesPosition => decide
  | stockLeg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegOpenCloseIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegOpenCloseIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegOpenCloseIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegOpenCloseIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegOpenCloseIndicator

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x43, 0x4F, 0x52, 0x50, 0x53, 0x49]

inductive AuctionType where
  | cola -- Cola
  | opening -- Opening
  | reopening -- Reopening
  | pixl -- Pixl
  | solicitation -- Solicitation
  | orderExposure -- Order Exposure
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .cola => 0x43
  | .opening => 0x4F
  | .reopening => 0x52
  | .pixl => 0x50
  | .solicitation => 0x53
  | .orderExposure => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x43 then .cola
  else if byte = 0x4F then .opening
  else if byte = 0x52 then .reopening
  else if byte = 0x50 then .pixl
  else if byte = 0x53 then .solicitation
  else .orderExposure

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | cola => decide
  | opening => decide
  | reopening => decide
  | pixl => decide
  | solicitation => decide
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

/-- Auction Side: one byte code -/
def AuctionSide.codes : List UInt8 :=
  [0x42, 0x53, 0x2A]

inductive AuctionSide where
  | buy -- Buy
  | sell -- Sell
  | solicitationAuction -- Solicitation Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionSide

def toByte : AuctionSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .solicitationAuction => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .solicitationAuction

def ofByte (byte : UInt8) : AuctionSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | solicitationAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AuctionSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionSide

/-- Timestamp: 8 bytes -/
structure Timestamp where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace Timestamp

def encode (message : Timestamp) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (Timestamp × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : Timestamp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : Timestamp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Timestamp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Timestamp

/-- System Event Message: 10 bytes -/
structure SystemEventMessage where
  timestamp : Timestamp
  eventCode : EventCode
  version : BitVec 8
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  Timestamp.encode message.timestamp
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 1 message.version))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← Timestamp.decode bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (version, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, eventCode, version }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Timestamp.encode_length, EventCode.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Timestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Options Directory Message: 40 bytes -/
structure OptionsDirectoryMessage where
  timestamp : Timestamp
  optionId : BitVec 32
  securitySymbol : Alpha 5
  expiration : BitVec 16
  explicitStrikePrice : BitVec 32
  optionType : OptionType
  source : BitVec 8
  underlyingSymbol : Alpha 13
  optionClosingType : OptionClosingType
  phlxTradable : PhlxTradable
  deriving DecidableEq, Repr

namespace OptionsDirectoryMessage

def encode (message : OptionsDirectoryMessage) : List UInt8 :=
  Timestamp.encode message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 2 message.expiration
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (encodeUInt 1 message.source
    ++ (Alpha.encode message.underlyingSymbol
    ++ (OptionClosingType.encode message.optionClosingType
    ++ (PhlxTradable.encode message.phlxTradable)))))))))

def decode (bytes : List UInt8) : Option (OptionsDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← Timestamp.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (expiration, bytes) ← decodeUInt 2 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (source, bytes) ← decodeUInt 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (optionClosingType, bytes) ← OptionClosingType.decode bytes
  let (phlxTradable, bytes) ← PhlxTradable.decode bytes
  pure ({ timestamp, optionId, securitySymbol, expiration, explicitStrikePrice, optionType, source, underlyingSymbol, optionClosingType, phlxTradable }, bytes)

@[simp] theorem encode_length (message : OptionsDirectoryMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Timestamp.encode_length, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, OptionClosingType.encode_length, PhlxTradable.encode_length]

theorem encode_length_pos (message : OptionsDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Timestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, OptionClosingType.decode_encode, some_bind]
  dsimp only
  rw [PhlxTradable.decode_encode, some_bind]
  rfl

end OptionsDirectoryMessage

/-- Complex Order Strategy Leg: 21 bytes -/
structure ComplexOrderStrategyLeg where
  optionId : BitVec 32
  securitySymbol : Alpha 5
  expiration : BitVec 16
  explicitStrikePrice : BitVec 32
  optionType : OptionType
  side : Side
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace ComplexOrderStrategyLeg

def encode (message : ComplexOrderStrategyLeg) : List UInt8 :=
  encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 2 message.expiration
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.legRatio))))))

def decode (bytes : List UInt8) : Option (ComplexOrderStrategyLeg × List UInt8) := do
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (expiration, bytes) ← decodeUInt 2 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (legRatio, bytes) ← decodeUInt 4 bytes
  pure ({ optionId, securitySymbol, expiration, explicitStrikePrice, optionType, side, legRatio }, bytes)

@[simp] theorem encode_length (message : ComplexOrderStrategyLeg) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, Side.encode_length]

theorem encode_length_pos (message : ComplexOrderStrategyLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexOrderStrategyLeg) (rest : List UInt8) :
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
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ComplexOrderStrategyLeg

/-- Complex Order Strategy Message -/
structure ComplexOrderStrategyMessage where
  timestamp : Timestamp
  strategyId : BitVec 32
  source : BitVec 8
  underlyingSymbol : Alpha 13
  action : Action
  complexOrderStrategyLeg : Bounded 1 ComplexOrderStrategyLeg
  deriving DecidableEq, Repr

namespace ComplexOrderStrategyMessage

def encode (message : ComplexOrderStrategyMessage) : List UInt8 :=
  Timestamp.encode message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 1 message.source
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Action.encode message.action
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.complexOrderStrategyLeg.val.length)
    ++ (encodeMany ComplexOrderStrategyLeg.encode message.complexOrderStrategyLeg.val))))))

def decode (bytes : List UInt8) : Option (ComplexOrderStrategyMessage × List UInt8) := do
  let (timestamp, bytes) ← Timestamp.decode bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (source, bytes) ← decodeUInt 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (action, bytes) ← Action.decode bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (complexOrderStrategyLeg_, bytes) ← decodeMany ComplexOrderStrategyLeg.decode numberOfLegs.toNat bytes
  if fits_complexOrderStrategyLeg : complexOrderStrategyLeg_.length < 256 ^ 1 then
    pure ({ timestamp, strategyId, source, underlyingSymbol, action, complexOrderStrategyLeg := ⟨complexOrderStrategyLeg_, fits_complexOrderStrategyLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexOrderStrategyMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Timestamp.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexOrderStrategyMessage) : (encode message).length ≤ 5383 := by
  have bound_complexOrderStrategyLeg := message.complexOrderStrategyLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Timestamp.encode_length, encodeUInt_length, Alpha.encode_length, Action.encode_length, encodeMany_length_const ComplexOrderStrategyLeg.encode 21 ComplexOrderStrategyLeg.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexOrderStrategyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Timestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Action.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 ComplexOrderStrategyLeg.encode ComplexOrderStrategyLeg.decode ComplexOrderStrategyLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.complexOrderStrategyLeg.length_lt]
  rfl

end ComplexOrderStrategyMessage

/-- Security Trading Action Message: 25 bytes -/
structure SecurityTradingActionMessage where
  timestamp : Timestamp
  optionId : BitVec 32
  securitySymbol : Alpha 5
  expiration : BitVec 16
  explicitStrikePrice : BitVec 32
  optionType : OptionType
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace SecurityTradingActionMessage

def encode (message : SecurityTradingActionMessage) : List UInt8 :=
  Timestamp.encode message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 2 message.expiration
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (CurrentTradingState.encode message.currentTradingState))))))

def decode (bytes : List UInt8) : Option (SecurityTradingActionMessage × List UInt8) := do
  let (timestamp, bytes) ← Timestamp.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (expiration, bytes) ← decodeUInt 2 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ timestamp, optionId, securitySymbol, expiration, explicitStrikePrice, optionType, currentTradingState }, bytes)

@[simp] theorem encode_length (message : SecurityTradingActionMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Timestamp.encode_length, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : SecurityTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Timestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [CurrentTradingState.decode_encode, some_bind]
  rfl

end SecurityTradingActionMessage

/-- Complex Trading Action Message: 13 bytes -/
structure ComplexTradingActionMessage where
  timestamp : Timestamp
  strategyId : BitVec 32
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace ComplexTradingActionMessage

def encode (message : ComplexTradingActionMessage) : List UInt8 :=
  Timestamp.encode message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (CurrentTradingState.encode message.currentTradingState))

def decode (bytes : List UInt8) : Option (ComplexTradingActionMessage × List UInt8) := do
  let (timestamp, bytes) ← Timestamp.decode bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ timestamp, strategyId, currentTradingState }, bytes)

@[simp] theorem encode_length (message : ComplexTradingActionMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, Timestamp.encode_length, encodeUInt_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : ComplexTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Timestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CurrentTradingState.decode_encode, some_bind]
  rfl

end ComplexTradingActionMessage

/-- Security Open Closed Message: 25 bytes -/
structure SecurityOpenClosedMessage where
  timestamp : Timestamp
  optionId : BitVec 32
  securitySymbol : Alpha 5
  expiration : BitVec 16
  explicitStrikePrice : BitVec 32
  optionType : OptionType
  openState : OpenState
  deriving DecidableEq, Repr

namespace SecurityOpenClosedMessage

def encode (message : SecurityOpenClosedMessage) : List UInt8 :=
  Timestamp.encode message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 2 message.expiration
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (OpenState.encode message.openState))))))

def decode (bytes : List UInt8) : Option (SecurityOpenClosedMessage × List UInt8) := do
  let (timestamp, bytes) ← Timestamp.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (expiration, bytes) ← decodeUInt 2 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (openState, bytes) ← OpenState.decode bytes
  pure ({ timestamp, optionId, securitySymbol, expiration, explicitStrikePrice, optionType, openState }, bytes)

@[simp] theorem encode_length (message : SecurityOpenClosedMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Timestamp.encode_length, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, OpenState.encode_length]

theorem encode_length_pos (message : SecurityOpenClosedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityOpenClosedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Timestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [OpenState.decode_encode, some_bind]
  rfl

end SecurityOpenClosedMessage

/-- Strategy Open Closed Message: 13 bytes -/
structure StrategyOpenClosedMessage where
  timestamp : Timestamp
  strategyId : BitVec 32
  openState : OpenState
  deriving DecidableEq, Repr

namespace StrategyOpenClosedMessage

def encode (message : StrategyOpenClosedMessage) : List UInt8 :=
  Timestamp.encode message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (OpenState.encode message.openState))

def decode (bytes : List UInt8) : Option (StrategyOpenClosedMessage × List UInt8) := do
  let (timestamp, bytes) ← Timestamp.decode bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (openState, bytes) ← OpenState.decode bytes
  pure ({ timestamp, strategyId, openState }, bytes)

@[simp] theorem encode_length (message : StrategyOpenClosedMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, Timestamp.encode_length, encodeUInt_length, OpenState.encode_length]

theorem encode_length_pos (message : StrategyOpenClosedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyOpenClosedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Timestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OpenState.decode_encode, some_bind]
  rfl

end StrategyOpenClosedMessage

/-- Simple Order Message: 48 bytes -/
structure SimpleOrderMessage where
  timestamp : Timestamp
  optionId : BitVec 32
  securitySymbol : Alpha 5
  expiration : BitVec 16
  explicitStrikePrice : BitVec 32
  optionType : OptionType
  orderId : BitVec 32
  side : Side
  originalOrderVolume : BitVec 32
  executableOrderVolume : BitVec 32
  orderStatus : OrderStatus
  orderType : OrderType
  marketQualifier : MarketQualifier
  limitPrice : BitVec 32
  allOrNone : AllOrNone
  timeInForce : TimeInForce
  customerFirmIndicator : CustomerFirmIndicator
  openCloseIndicator : OpenCloseIndicator
  deriving DecidableEq, Repr

namespace SimpleOrderMessage

def encode (message : SimpleOrderMessage) : List UInt8 :=
  Timestamp.encode message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 2 message.expiration
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (encodeUInt 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.originalOrderVolume
    ++ (encodeUInt 4 message.executableOrderVolume
    ++ (OrderStatus.encode message.orderStatus
    ++ (OrderType.encode message.orderType
    ++ (MarketQualifier.encode message.marketQualifier
    ++ (encodeUInt 4 message.limitPrice
    ++ (AllOrNone.encode message.allOrNone
    ++ (TimeInForce.encode message.timeInForce
    ++ (CustomerFirmIndicator.encode message.customerFirmIndicator
    ++ (OpenCloseIndicator.encode message.openCloseIndicator)))))))))))))))))

def decode (bytes : List UInt8) : Option (SimpleOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← Timestamp.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (expiration, bytes) ← decodeUInt 2 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (orderId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (originalOrderVolume, bytes) ← decodeUInt 4 bytes
  let (executableOrderVolume, bytes) ← decodeUInt 4 bytes
  let (orderStatus, bytes) ← OrderStatus.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (marketQualifier, bytes) ← MarketQualifier.decode bytes
  let (limitPrice, bytes) ← decodeUInt 4 bytes
  let (allOrNone, bytes) ← AllOrNone.decode bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (customerFirmIndicator, bytes) ← CustomerFirmIndicator.decode bytes
  let (openCloseIndicator, bytes) ← OpenCloseIndicator.decode bytes
  pure ({ timestamp, optionId, securitySymbol, expiration, explicitStrikePrice, optionType, orderId, side, originalOrderVolume, executableOrderVolume, orderStatus, orderType, marketQualifier, limitPrice, allOrNone, timeInForce, customerFirmIndicator, openCloseIndicator }, bytes)

@[simp] theorem encode_length (message : SimpleOrderMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, Timestamp.encode_length, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, Side.encode_length, OrderStatus.encode_length, OrderType.encode_length, MarketQualifier.encode_length, AllOrNone.encode_length, TimeInForce.encode_length, CustomerFirmIndicator.encode_length, OpenCloseIndicator.encode_length]

theorem encode_length_pos (message : SimpleOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Timestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketQualifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AllOrNone.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustomerFirmIndicator.decode_encode, some_bind]
  dsimp only
  rw [OpenCloseIndicator.decode_encode, some_bind]
  rfl

end SimpleOrderMessage

/-- Complex Order Leg: 22 bytes -/
structure ComplexOrderLeg where
  legOpenCloseIndicator : LegOpenCloseIndicator
  optionId : BitVec 32
  securitySymbol : Alpha 5
  expiration : BitVec 16
  explicitStrikePrice : BitVec 32
  optionType : OptionType
  side : Side
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace ComplexOrderLeg

def encode (message : ComplexOrderLeg) : List UInt8 :=
  LegOpenCloseIndicator.encode message.legOpenCloseIndicator
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 2 message.expiration
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.legRatio)))))))

def decode (bytes : List UInt8) : Option (ComplexOrderLeg × List UInt8) := do
  let (legOpenCloseIndicator, bytes) ← LegOpenCloseIndicator.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (expiration, bytes) ← decodeUInt 2 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (legRatio, bytes) ← decodeUInt 4 bytes
  pure ({ legOpenCloseIndicator, optionId, securitySymbol, expiration, explicitStrikePrice, optionType, side, legRatio }, bytes)

@[simp] theorem encode_length (message : ComplexOrderLeg) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, LegOpenCloseIndicator.encode_length, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, Side.encode_length]

theorem encode_length_pos (message : ComplexOrderLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexOrderLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LegOpenCloseIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ComplexOrderLeg

/-- Complex Order Message -/
structure ComplexOrderMessage where
  timestamp : Timestamp
  strategyId : BitVec 32
  orderId : BitVec 32
  side : Side
  originalOrderVolume : BitVec 32
  executableOrderVolume : BitVec 32
  orderStatus : OrderStatus
  orderType : OrderType
  limitPrice : BitVec 32
  debitOrCredit : DebitOrCredit
  allOrNone : AllOrNone
  timeInForce : TimeInForce
  customerFirmIndicator : CustomerFirmIndicator
  underlyingSymbol : Alpha 13
  complexOrderLeg : Bounded 1 ComplexOrderLeg
  deriving DecidableEq, Repr

namespace ComplexOrderMessage

def encode (message : ComplexOrderMessage) : List UInt8 :=
  Timestamp.encode message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.originalOrderVolume
    ++ (encodeUInt 4 message.executableOrderVolume
    ++ (OrderStatus.encode message.orderStatus
    ++ (OrderType.encode message.orderType
    ++ (encodeUInt 4 message.limitPrice
    ++ (DebitOrCredit.encode message.debitOrCredit
    ++ (AllOrNone.encode message.allOrNone
    ++ (TimeInForce.encode message.timeInForce
    ++ (CustomerFirmIndicator.encode message.customerFirmIndicator
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.complexOrderLeg.val.length)
    ++ (encodeMany ComplexOrderLeg.encode message.complexOrderLeg.val)))))))))))))))

def decode (bytes : List UInt8) : Option (ComplexOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← Timestamp.decode bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (originalOrderVolume, bytes) ← decodeUInt 4 bytes
  let (executableOrderVolume, bytes) ← decodeUInt 4 bytes
  let (orderStatus, bytes) ← OrderStatus.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (limitPrice, bytes) ← decodeUInt 4 bytes
  let (debitOrCredit, bytes) ← DebitOrCredit.decode bytes
  let (allOrNone, bytes) ← AllOrNone.decode bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (customerFirmIndicator, bytes) ← CustomerFirmIndicator.decode bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (complexOrderLeg_, bytes) ← decodeMany ComplexOrderLeg.decode numberOfLegs.toNat bytes
  if fits_complexOrderLeg : complexOrderLeg_.length < 256 ^ 1 then
    pure ({ timestamp, strategyId, orderId, side, originalOrderVolume, executableOrderVolume, orderStatus, orderType, limitPrice, debitOrCredit, allOrNone, timeInForce, customerFirmIndicator, underlyingSymbol, complexOrderLeg := ⟨complexOrderLeg_, fits_complexOrderLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Timestamp.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexOrderMessage) : (encode message).length ≤ 5659 := by
  have bound_complexOrderLeg := message.complexOrderLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Timestamp.encode_length, encodeUInt_length, Side.encode_length, OrderStatus.encode_length, OrderType.encode_length, DebitOrCredit.encode_length, AllOrNone.encode_length, TimeInForce.encode_length, CustomerFirmIndicator.encode_length, Alpha.encode_length, encodeMany_length_const ComplexOrderLeg.encode 22 ComplexOrderLeg.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Timestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, DebitOrCredit.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AllOrNone.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustomerFirmIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 ComplexOrderLeg.encode ComplexOrderLeg.decode ComplexOrderLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.complexOrderLeg.length_lt]
  rfl

end ComplexOrderMessage

/-- Auction Notification Message: 46 bytes -/
structure AuctionNotificationMessage where
  timestamp : Timestamp
  optionId : BitVec 32
  securitySymbol : Alpha 5
  expiration : BitVec 16
  explicitStrikePrice : BitVec 32
  optionType : OptionType
  auctionId : BitVec 32
  auctionType : AuctionType
  price : BitVec 32
  auctionSide : AuctionSide
  matchedVolume : BitVec 32
  imbalanceVolume : BitVec 32
  reserved4 : BitVec 32
  deriving DecidableEq, Repr

namespace AuctionNotificationMessage

def encode (message : AuctionNotificationMessage) : List UInt8 :=
  Timestamp.encode message.timestamp
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 2 message.expiration
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (encodeUInt 4 message.auctionId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.price
    ++ (AuctionSide.encode message.auctionSide
    ++ (encodeUInt 4 message.matchedVolume
    ++ (encodeUInt 4 message.imbalanceVolume
    ++ (encodeUInt 4 message.reserved4))))))))))))

def decode (bytes : List UInt8) : Option (AuctionNotificationMessage × List UInt8) := do
  let (timestamp, bytes) ← Timestamp.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (expiration, bytes) ← decodeUInt 2 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (auctionSide, bytes) ← AuctionSide.decode bytes
  let (matchedVolume, bytes) ← decodeUInt 4 bytes
  let (imbalanceVolume, bytes) ← decodeUInt 4 bytes
  let (reserved4, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, optionId, securitySymbol, expiration, explicitStrikePrice, optionType, auctionId, auctionType, price, auctionSide, matchedVolume, imbalanceVolume, reserved4 }, bytes)

@[simp] theorem encode_length (message : AuctionNotificationMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Timestamp.encode_length, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, AuctionType.encode_length, AuctionSide.encode_length]

theorem encode_length_pos (message : AuctionNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Timestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AuctionNotificationMessage

/-- Complex Auction Notification Message: 27 bytes -/
structure ComplexAuctionNotificationMessage where
  timestamp : Timestamp
  strategyId : BitVec 32
  auctionId : BitVec 32
  auctionType : AuctionType
  price : BitVec 32
  auctionSide : AuctionSide
  debitOrCredit : DebitOrCredit
  volume : BitVec 32
  deriving DecidableEq, Repr

namespace ComplexAuctionNotificationMessage

def encode (message : ComplexAuctionNotificationMessage) : List UInt8 :=
  Timestamp.encode message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 4 message.auctionId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.price
    ++ (AuctionSide.encode message.auctionSide
    ++ (DebitOrCredit.encode message.debitOrCredit
    ++ (encodeUInt 4 message.volume)))))))

def decode (bytes : List UInt8) : Option (ComplexAuctionNotificationMessage × List UInt8) := do
  let (timestamp, bytes) ← Timestamp.decode bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (auctionSide, bytes) ← AuctionSide.decode bytes
  let (debitOrCredit, bytes) ← DebitOrCredit.decode bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, strategyId, auctionId, auctionType, price, auctionSide, debitOrCredit, volume }, bytes)

@[simp] theorem encode_length (message : ComplexAuctionNotificationMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, Timestamp.encode_length, encodeUInt_length, AuctionType.encode_length, AuctionSide.encode_length, DebitOrCredit.encode_length]

theorem encode_length_pos (message : ComplexAuctionNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexAuctionNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Timestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DebitOrCredit.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ComplexAuctionNotificationMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | optionsDirectoryMessage (message : OptionsDirectoryMessage) -- "D" 0x44
  | complexOrderStrategyMessage (message : ComplexOrderStrategyMessage) -- "R" 0x52
  | securityTradingActionMessage (message : SecurityTradingActionMessage) -- "H" 0x48
  | complexTradingActionMessage (message : ComplexTradingActionMessage) -- "I" 0x49
  | securityOpenClosedMessage (message : SecurityOpenClosedMessage) -- "P" 0x50
  | strategyOpenClosedMessage (message : StrategyOpenClosedMessage) -- "Q" 0x51
  | simpleOrderMessage (message : SimpleOrderMessage) -- "O" 0x4F
  | complexOrderMessage (message : ComplexOrderMessage) -- "X" 0x58
  | auctionNotificationMessage (message : AuctionNotificationMessage) -- "A" 0x41
  | complexAuctionNotificationMessage (message : ComplexAuctionNotificationMessage) -- "C" 0x43
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .optionsDirectoryMessage _ => 68
  | .complexOrderStrategyMessage _ => 82
  | .securityTradingActionMessage _ => 72
  | .complexTradingActionMessage _ => 73
  | .securityOpenClosedMessage _ => 80
  | .strategyOpenClosedMessage _ => 81
  | .simpleOrderMessage _ => 79
  | .complexOrderMessage _ => 88
  | .auctionNotificationMessage _ => 65
  | .complexAuctionNotificationMessage _ => 67

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .optionsDirectoryMessage message => OptionsDirectoryMessage.encode message
  | .complexOrderStrategyMessage message => ComplexOrderStrategyMessage.encode message
  | .securityTradingActionMessage message => SecurityTradingActionMessage.encode message
  | .complexTradingActionMessage message => ComplexTradingActionMessage.encode message
  | .securityOpenClosedMessage message => SecurityOpenClosedMessage.encode message
  | .strategyOpenClosedMessage message => StrategyOpenClosedMessage.encode message
  | .simpleOrderMessage message => SimpleOrderMessage.encode message
  | .complexOrderMessage message => ComplexOrderMessage.encode message
  | .auctionNotificationMessage message => AuctionNotificationMessage.encode message
  | .complexAuctionNotificationMessage message => ComplexAuctionNotificationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 5659 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | optionsDirectoryMessage inner =>
    simp only [encode, OptionsDirectoryMessage.encode_length]
    omega
  | complexOrderStrategyMessage inner =>
    have bound_inner := ComplexOrderStrategyMessage.encode_length_le inner
    simp only [encode]
    omega
  | securityTradingActionMessage inner =>
    simp only [encode, SecurityTradingActionMessage.encode_length]
    omega
  | complexTradingActionMessage inner =>
    simp only [encode, ComplexTradingActionMessage.encode_length]
    omega
  | securityOpenClosedMessage inner =>
    simp only [encode, SecurityOpenClosedMessage.encode_length]
    omega
  | strategyOpenClosedMessage inner =>
    simp only [encode, StrategyOpenClosedMessage.encode_length]
    omega
  | simpleOrderMessage inner =>
    simp only [encode, SimpleOrderMessage.encode_length]
    omega
  | complexOrderMessage inner =>
    have bound_inner := ComplexOrderMessage.encode_length_le inner
    simp only [encode]
    omega
  | auctionNotificationMessage inner =>
    simp only [encode, AuctionNotificationMessage.encode_length]
    omega
  | complexAuctionNotificationMessage inner =>
    simp only [encode, ComplexAuctionNotificationMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 68 then (OptionsDirectoryMessage.decode bytes).map fun (message, rest) => (.optionsDirectoryMessage message, rest)
  else if tag = 82 then (ComplexOrderStrategyMessage.decode bytes).map fun (message, rest) => (.complexOrderStrategyMessage message, rest)
  else if tag = 72 then (SecurityTradingActionMessage.decode bytes).map fun (message, rest) => (.securityTradingActionMessage message, rest)
  else if tag = 73 then (ComplexTradingActionMessage.decode bytes).map fun (message, rest) => (.complexTradingActionMessage message, rest)
  else if tag = 80 then (SecurityOpenClosedMessage.decode bytes).map fun (message, rest) => (.securityOpenClosedMessage message, rest)
  else if tag = 81 then (StrategyOpenClosedMessage.decode bytes).map fun (message, rest) => (.strategyOpenClosedMessage message, rest)
  else if tag = 79 then (SimpleOrderMessage.decode bytes).map fun (message, rest) => (.simpleOrderMessage message, rest)
  else if tag = 88 then (ComplexOrderMessage.decode bytes).map fun (message, rest) => (.complexOrderMessage message, rest)
  else if tag = 65 then (AuctionNotificationMessage.decode bytes).map fun (message, rest) => (.auctionNotificationMessage message, rest)
  else if tag = 67 then (ComplexAuctionNotificationMessage.decode bytes).map fun (message, rest) => (.complexAuctionNotificationMessage message, rest)
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
  | optionsDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OptionsDirectoryMessage.encode_length]
    omega
  | complexOrderStrategyMessage inner =>
    have bound_inner := ComplexOrderStrategyMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUInt_length]
    omega
  | securityTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityTradingActionMessage.encode_length]
    omega
  | complexTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ComplexTradingActionMessage.encode_length]
    omega
  | securityOpenClosedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityOpenClosedMessage.encode_length]
    omega
  | strategyOpenClosedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StrategyOpenClosedMessage.encode_length]
    omega
  | simpleOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SimpleOrderMessage.encode_length]
    omega
  | complexOrderMessage inner =>
    have bound_inner := ComplexOrderMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUInt_length]
    omega
  | auctionNotificationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AuctionNotificationMessage.encode_length]
    omega
  | complexAuctionNotificationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ComplexAuctionNotificationMessage.encode_length]
    omega

/-- Size rule: Length counts the bytes after it, so it is written from the body and checked on decode -/
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
  sequence : BitVec 32
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 4 message.sequence
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequence, bytes) ← decodeUInt 4 bytes
  let (count, bytes) ← decodeUIntLE 2 bytes
  let (message_, bytes) ← decodeMany Message.decode count.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequence, message := ⟨message_, fits_message⟩ }, bytes)
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NasdaqPhlxoptionsOrdersItchV19
