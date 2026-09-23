import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Order Feed v2.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqGemxoptionsOrderfeedItchV21Udp

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
  [0x43, 0x50, 0x4E]

inductive OptionType where
  | call -- Call
  | put -- Put
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .call => 0x43
  | .put => 0x50
  | .notApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .call
  else if byte = 0x50 then .put
  else .notApplicable

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | notApplicable => decide
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
  [0x4E, 0x4C, 0x57]

inductive ClosingType where
  | normalHours -- Normal Hours
  | lateHours -- Late Hours
  | wcoEarlyClosing -- Wco Early Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ ClosingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClosingType

def toByte : ClosingType → UInt8
  | .normalHours => 0x4E
  | .lateHours => 0x4C
  | .wcoEarlyClosing => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClosingType :=
  if byte = 0x4E then .normalHours
  else if byte = 0x4C then .lateHours
  else .wcoEarlyClosing

def ofByte (byte : UInt8) : ClosingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClosingType) : ofByte value.toByte = value := by
  cases value with
  | normalHours => decide
  | lateHours => decide
  | wcoEarlyClosing => decide
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
  [0x42, 0x53, 0x48, 0x54, 0x49, 0x4F, 0x52, 0x58]

inductive CurrentTradingState where
  | buySideSuspended -- Buy Side Suspended
  | sellSideSuspended -- Sell Side Suspended
  | haltInEffect -- Halt In Effect
  | continuousTrading -- Continuous Trading
  | preOpen -- Pre Open
  | openingAuction -- Opening Auction
  | reOpening -- Re Opening
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .buySideSuspended => 0x42
  | .sellSideSuspended => 0x53
  | .haltInEffect => 0x48
  | .continuousTrading => 0x54
  | .preOpen => 0x49
  | .openingAuction => 0x4F
  | .reOpening => 0x52
  | .closed => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x42 then .buySideSuspended
  else if byte = 0x53 then .sellSideSuspended
  else if byte = 0x48 then .haltInEffect
  else if byte = 0x54 then .continuousTrading
  else if byte = 0x49 then .preOpen
  else if byte = 0x4F then .openingAuction
  else if byte = 0x52 then .reOpening
  else .closed

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | buySideSuspended => decide
  | sellSideSuspended => decide
  | haltInEffect => decide
  | continuousTrading => decide
  | preOpen => decide
  | openingAuction => decide
  | reOpening => decide
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

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
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

/-- Order Status: one byte code -/
def OrderStatus.codes : List UInt8 :=
  [0x4F, 0x46, 0x43]

inductive OrderStatus where
  | open_ -- Open
  | filled -- Filled
  | cancelled -- Cancelled
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderStatus

def toByte : OrderStatus → UInt8
  | .open_ => 0x4F
  | .filled => 0x46
  | .cancelled => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderStatus :=
  if byte = 0x4F then .open_
  else if byte = 0x46 then .filled
  else .cancelled

def ofByte (byte : UInt8) : OrderStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderStatus) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | filled => decide
  | cancelled => decide
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

/-- Order Qualifier: one byte code -/
def OrderQualifier.codes : List UInt8 :=
  [0x4F, 0x49, 0x20]

inductive OrderQualifier where
  | openingOrder -- Opening Order
  | impliedOrder -- Implied Order
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderQualifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderQualifier

def toByte : OrderQualifier → UInt8
  | .openingOrder => 0x4F
  | .impliedOrder => 0x49
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderQualifier :=
  if byte = 0x4F then .openingOrder
  else if byte = 0x49 then .impliedOrder
  else .na

def ofByte (byte : UInt8) : OrderQualifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderQualifier) : ofByte value.toByte = value := by
  cases value with
  | openingOrder => decide
  | impliedOrder => decide
  | na => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderQualifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderQualifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderQualifier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderQualifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderQualifier

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
  [0x44, 0x47]

inductive TimeInForce where
  | dayOrder -- Day Order
  | goodTillCancelled -- Good Till Cancelled
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForce

def toByte : TimeInForce → UInt8
  | .dayOrder => 0x44
  | .goodTillCancelled => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForce :=
  if byte = 0x44 then .dayOrder
  else .goodTillCancelled

def ofByte (byte : UInt8) : TimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForce) : ofByte value.toByte = value := by
  cases value with
  | dayOrder => decide
  | goodTillCancelled => decide
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

/-- Order Capacity: one byte code -/
def OrderCapacity.codes : List UInt8 :=
  [0x43, 0x46, 0x4D, 0x42, 0x50, 0x4F, 0x4A, 0x20]

inductive OrderCapacity where
  | customerOrder -- Customer Order
  | firmOrder -- Firm Order
  | marketMakerOrder -- Market Maker Order
  | brokerDealerOrder -- Broker Dealer Order
  | professionalOrder -- Professional Order
  | otherExchangeMarketMakerOrder -- Other Exchange Market Maker Order
  | jointBackOffice -- Joint Back Office
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderCapacity

def toByte : OrderCapacity → UInt8
  | .customerOrder => 0x43
  | .firmOrder => 0x46
  | .marketMakerOrder => 0x4D
  | .brokerDealerOrder => 0x42
  | .professionalOrder => 0x50
  | .otherExchangeMarketMakerOrder => 0x4F
  | .jointBackOffice => 0x4A
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderCapacity :=
  if byte = 0x43 then .customerOrder
  else if byte = 0x46 then .firmOrder
  else if byte = 0x4D then .marketMakerOrder
  else if byte = 0x42 then .brokerDealerOrder
  else if byte = 0x50 then .professionalOrder
  else if byte = 0x4F then .otherExchangeMarketMakerOrder
  else if byte = 0x4A then .jointBackOffice
  else .na

def ofByte (byte : UInt8) : OrderCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderCapacity) : ofByte value.toByte = value := by
  cases value with
  | customerOrder => decide
  | firmOrder => decide
  | marketMakerOrder => decide
  | brokerDealerOrder => decide
  | professionalOrder => decide
  | otherExchangeMarketMakerOrder => decide
  | jointBackOffice => decide
  | na => decide
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

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x42, 0x4F, 0x52, 0x49, 0x50, 0x43, 0x53, 0x58]

inductive AuctionType where
  | blockAuction -- Block Auction
  | opening -- Opening
  | reopening -- Reopening
  | orderExposure -- Order Exposure
  | priceImprovementAuction -- Price Improvement Auction
  | facilitation -- Facilitation
  | solicitation -- Solicitation
  | flexAuction -- Flex Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .blockAuction => 0x42
  | .opening => 0x4F
  | .reopening => 0x52
  | .orderExposure => 0x49
  | .priceImprovementAuction => 0x50
  | .facilitation => 0x43
  | .solicitation => 0x53
  | .flexAuction => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x42 then .blockAuction
  else if byte = 0x4F then .opening
  else if byte = 0x52 then .reopening
  else if byte = 0x49 then .orderExposure
  else if byte = 0x50 then .priceImprovementAuction
  else if byte = 0x43 then .facilitation
  else if byte = 0x53 then .solicitation
  else .flexAuction

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | blockAuction => decide
  | opening => decide
  | reopening => decide
  | orderExposure => decide
  | priceImprovementAuction => decide
  | facilitation => decide
  | solicitation => decide
  | flexAuction => decide
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

/-- Auction Event: one byte code -/
def AuctionEvent.codes : List UInt8 :=
  [0x53, 0x45, 0x55]

inductive AuctionEvent where
  | startOfAuction -- Start Of Auction
  | endOfAuction -- End Of Auction
  | auctionUpdate -- Auction Update
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionEvent.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionEvent

def toByte : AuctionEvent → UInt8
  | .startOfAuction => 0x53
  | .endOfAuction => 0x45
  | .auctionUpdate => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionEvent :=
  if byte = 0x53 then .startOfAuction
  else if byte = 0x45 then .endOfAuction
  else .auctionUpdate

def ofByte (byte : UInt8) : AuctionEvent :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionEvent) : ofByte value.toByte = value := by
  cases value with
  | startOfAuction => decide
  | endOfAuction => decide
  | auctionUpdate => decide
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

/-- Exec Flag: one byte code -/
def ExecFlag.codes : List UInt8 :=
  [0x4E, 0x41]

inductive ExecFlag where
  | none_ -- None
  | aon -- Aon
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecFlag

def toByte : ExecFlag → UInt8
  | .none_ => 0x4E
  | .aon => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecFlag :=
  if byte = 0x4E then .none_
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

/-- Derivative Directory Message: 62 bytes -/
structure DerivativeDirectoryMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  securitySymbol : Alpha 8
  expirationYear : BitVec 8
  expirationMonth : BitVec 8
  expirationDay : BitVec 8
  explicitStrikePrice : BitVec 32
  optionType : OptionType
  underlyingSymbol : Alpha 13
  closingType : ClosingType
  tradable : Tradable
  mpv : Mpv
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace DerivativeDirectoryMessage

def encode (message : DerivativeDirectoryMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 1 message.expirationYear
    ++ (encodeUInt 1 message.expirationMonth
    ++ (encodeUInt 1 message.expirationDay
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.underlyingSymbol
    ++ (ClosingType.encode message.closingType
    ++ (Tradable.encode message.tradable
    ++ (Mpv.encode message.mpv
    ++ (Alpha.encode message.reserved16)))))))))))))

def decode (bytes : List UInt8) : Option (DerivativeDirectoryMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 8 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  let (expirationMonth, bytes) ← decodeUInt 1 bytes
  let (expirationDay, bytes) ← decodeUInt 1 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (closingType, bytes) ← ClosingType.decode bytes
  let (tradable_, bytes) ← Tradable.decode bytes
  let (mpv, bytes) ← Mpv.decode bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ trackingNumber, timestamp, instrumentId, securitySymbol, expirationYear, expirationMonth, expirationDay, explicitStrikePrice, optionType, underlyingSymbol, closingType, tradable := tradable_, mpv, reserved16 }, bytes)

@[simp] theorem encode_length (message : DerivativeDirectoryMessage) : (encode message).length = 62 := by
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

/-- Add Order Message: 60 bytes -/
structure AddOrderMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderReferenceNumber : BitVec 64
  side : Side
  originalOrderVolume : BitVec 32
  executableOrderVolume : BitVec 32
  orderStatus : OrderStatus
  orderType : OrderType
  orderQualifier : OrderQualifier
  limitPrice : BitVec 32
  allOrNone : AllOrNone
  timeInForce : TimeInForce
  orderCapacity : OrderCapacity
  openCloseIndicator : OpenCloseIndicator
  ownerId : Alpha 6
  giveup : Alpha 6
  cmta : Alpha 6
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.originalOrderVolume
    ++ (encodeUInt 4 message.executableOrderVolume
    ++ (OrderStatus.encode message.orderStatus
    ++ (OrderType.encode message.orderType
    ++ (OrderQualifier.encode message.orderQualifier
    ++ (encodeUInt 4 message.limitPrice
    ++ (AllOrNone.encode message.allOrNone
    ++ (TimeInForce.encode message.timeInForce
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (OpenCloseIndicator.encode message.openCloseIndicator
    ++ (Alpha.encode message.ownerId
    ++ (Alpha.encode message.giveup
    ++ (Alpha.encode message.cmta)))))))))))))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (originalOrderVolume, bytes) ← decodeUInt 4 bytes
  let (executableOrderVolume, bytes) ← decodeUInt 4 bytes
  let (orderStatus, bytes) ← OrderStatus.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (orderQualifier, bytes) ← OrderQualifier.decode bytes
  let (limitPrice, bytes) ← decodeUInt 4 bytes
  let (allOrNone, bytes) ← AllOrNone.decode bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (openCloseIndicator, bytes) ← OpenCloseIndicator.decode bytes
  let (ownerId, bytes) ← Alpha.decode 6 bytes
  let (giveup, bytes) ← Alpha.decode 6 bytes
  let (cmta, bytes) ← Alpha.decode 6 bytes
  pure ({ trackingNumber, timestamp, instrumentId, orderReferenceNumber, side, originalOrderVolume, executableOrderVolume, orderStatus, orderType, orderQualifier, limitPrice, allOrNone, timeInForce, orderCapacity, openCloseIndicator, ownerId, giveup, cmta }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, OrderStatus.encode_length, OrderType.encode_length, OrderQualifier.encode_length, AllOrNone.encode_length, TimeInForce.encode_length, OrderCapacity.encode_length, OpenCloseIndicator.encode_length, Alpha.encode_length]

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
  rw [List.append_assoc, OrderQualifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AllOrNone.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenCloseIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderMessage

/-- Auction Message: 73 bytes -/
structure AuctionMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  auctionId : BitVec 32
  auctionType : AuctionType
  auctionDuration : BitVec 32
  auctionEvent : AuctionEvent
  quantity : BitVec 32
  side : Side
  price : BitVec 32
  imbalanceVolume : BitVec 32
  execFlag : ExecFlag
  orderCapacity : OrderCapacity
  ownerId : Alpha 6
  giveup : Alpha 6
  cmta : Alpha 6
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace AuctionMessage

def encode (message : AuctionMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.auctionId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.auctionDuration
    ++ (AuctionEvent.encode message.auctionEvent
    ++ (encodeUInt 4 message.quantity
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.imbalanceVolume
    ++ (ExecFlag.encode message.execFlag
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (Alpha.encode message.ownerId
    ++ (Alpha.encode message.giveup
    ++ (Alpha.encode message.cmta
    ++ (Alpha.encode message.reserved16))))))))))))))))

def decode (bytes : List UInt8) : Option (AuctionMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (auctionDuration, bytes) ← decodeUInt 4 bytes
  let (auctionEvent, bytes) ← AuctionEvent.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (imbalanceVolume, bytes) ← decodeUInt 4 bytes
  let (execFlag, bytes) ← ExecFlag.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (ownerId, bytes) ← Alpha.decode 6 bytes
  let (giveup, bytes) ← Alpha.decode 6 bytes
  let (cmta, bytes) ← Alpha.decode 6 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ trackingNumber, timestamp, instrumentId, auctionId, auctionType, auctionDuration, auctionEvent, quantity, side, price, imbalanceVolume, execFlag, orderCapacity, ownerId, giveup, cmta, reserved16 }, bytes)

@[simp] theorem encode_length (message : AuctionMessage) : (encode message).length = 73 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, AuctionType.encode_length, AuctionEvent.encode_length, Side.encode_length, ExecFlag.encode_length, OrderCapacity.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AuctionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, AuctionEvent.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end AuctionMessage

/-- Any Udp Payload, selected by Message Type -/
inductive UdpPayload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | derivativeDirectoryMessage (message : DerivativeDirectoryMessage) -- "m" 0x6D
  | tradingActionMessage (message : TradingActionMessage) -- "H" 0x48
  | addOrderMessage (message : AddOrderMessage) -- "O" 0x4F
  | auctionMessage (message : AuctionMessage) -- "J" 0x4A
  deriving DecidableEq, Repr

namespace UdpPayload

/-- The Message Type each message is sent under -/
def tag : UdpPayload → BitVec 8
  | .systemEventMessage _ => 83
  | .derivativeDirectoryMessage _ => 109
  | .tradingActionMessage _ => 72
  | .addOrderMessage _ => 79
  | .auctionMessage _ => 74

def encode : UdpPayload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .derivativeDirectoryMessage message => DerivativeDirectoryMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .auctionMessage message => AuctionMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UdpPayload) : (encode message).length ≤ 73 := by
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
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | auctionMessage inner =>
    simp only [encode, AuctionMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UdpPayload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 109 then (DerivativeDirectoryMessage.decode bytes).map fun (message, rest) => (.derivativeDirectoryMessage message, rest)
  else if tag = 72 then (TradingActionMessage.decode bytes).map fun (message, rest) => (.tradingActionMessage message, rest)
  else if tag = 79 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 74 then (AuctionMessage.decode bytes).map fun (message, rest) => (.auctionMessage message, rest)
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
  | derivativeDirectoryMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, DerivativeDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, TradingActionMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | auctionMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, AuctionMessage.encode_length]
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
  udpSession : Alpha 10
  udpSequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.udpSession
    ++ (encodeUInt 8 message.udpSequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (udpSession, bytes) ← Alpha.decode 10 bytes
  let (udpSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ udpSession, udpSequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
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

end Omi.NasdaqGemxoptionsOrderfeedItchV21Udp
