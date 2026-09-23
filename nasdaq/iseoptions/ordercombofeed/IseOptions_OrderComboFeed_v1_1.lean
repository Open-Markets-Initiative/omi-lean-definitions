import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Ise Order Combo Market Data Feed v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqIseoptionsOrdercombofeedItchV11

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

/-- Strategy Type: one byte code -/
def StrategyType.codes : List UInt8 :=
  [0x56, 0x54, 0x44, 0x53, 0x47, 0x43, 0x52, 0x41, 0x55]

inductive StrategyType where
  | verticalSpread -- Vertical Spread
  | timeSpread -- Time Spread
  | diagonalSpread -- Diagonal Spread
  | straddle -- Straddle
  | strangle -- Strangle
  | combo -- Combo
  | riskReversal -- Risk Reversal
  | ratioSpread -- Ratio Spread
  | custom -- Custom
  | unlisted (byte : { byte : UInt8 // byte ∉ StrategyType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrategyType

def toByte : StrategyType → UInt8
  | .verticalSpread => 0x56
  | .timeSpread => 0x54
  | .diagonalSpread => 0x44
  | .straddle => 0x53
  | .strangle => 0x47
  | .combo => 0x43
  | .riskReversal => 0x52
  | .ratioSpread => 0x41
  | .custom => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrategyType :=
  if byte = 0x56 then .verticalSpread
  else if byte = 0x54 then .timeSpread
  else if byte = 0x44 then .diagonalSpread
  else if byte = 0x53 then .straddle
  else if byte = 0x47 then .strangle
  else if byte = 0x43 then .combo
  else if byte = 0x52 then .riskReversal
  else if byte = 0x41 then .ratioSpread
  else .custom

def ofByte (byte : UInt8) : StrategyType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrategyType) : ofByte value.toByte = value := by
  cases value with
  | verticalSpread => decide
  | timeSpread => decide
  | diagonalSpread => decide
  | straddle => decide
  | strangle => decide
  | combo => decide
  | riskReversal => decide
  | ratioSpread => decide
  | custom => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrategyType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrategyType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrategyType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StrategyType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrategyType

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x43, 0x50, 0x20]

inductive OptionType where
  | call -- Call
  | put -- Put
  | stock -- Stock
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .call => 0x43
  | .put => 0x50
  | .stock => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .call
  else if byte = 0x50 then .put
  else .stock

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | stock => decide
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

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x48, 0x54]

inductive CurrentTradingState where
  | haltInEffect -- Halt In Effect
  | tradingResumed -- Trading Resumed
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .haltInEffect => 0x48
  | .tradingResumed => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .haltInEffect
  else .tradingResumed

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | haltInEffect => decide
  | tradingResumed => decide
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

/-- Scope: one byte code -/
def Scope.codes : List UInt8 :=
  [0x4C, 0x4E]

inductive Scope where
  | local_ -- Local
  | national -- National
  | unlisted (byte : { byte : UInt8 // byte ∉ Scope.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Scope

def toByte : Scope → UInt8
  | .local_ => 0x4C
  | .national => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Scope :=
  if byte = 0x4C then .local_
  else .national

def ofByte (byte : UInt8) : Scope :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Scope) : ofByte value.toByte = value := by
  cases value with
  | local_ => decide
  | national => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Scope) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Scope × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Scope) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Scope) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Scope

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
  [0x45, 0x43, 0x53, 0x50]

inductive AuctionType where
  | exposure -- Exposure
  | facilitation -- Facilitation
  | solicitation -- Solicitation
  | pim -- Pim
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .exposure => 0x45
  | .facilitation => 0x43
  | .solicitation => 0x53
  | .pim => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x45 then .exposure
  else if byte = 0x43 then .facilitation
  else if byte = 0x53 then .solicitation
  else .pim

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | exposure => decide
  | facilitation => decide
  | solicitation => decide
  | pim => decide
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

/-- Leg Information: 28 bytes -/
structure LegInformation where
  optionId : BitVec 32
  securitySymbol : Alpha 6
  legId : BitVec 8
  expirationYear : BitVec 8
  expirationMonth : BitVec 8
  expirationDay : BitVec 8
  explicitStrikePrice : BitVec 64
  optionType : OptionType
  legSide : LegSide
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace LegInformation

def encode (message : LegInformation) : List UInt8 :=
  encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 1 message.legId
    ++ (encodeUInt 1 message.expirationYear
    ++ (encodeUInt 1 message.expirationMonth
    ++ (encodeUInt 1 message.expirationDay
    ++ (encodeUInt 8 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (LegSide.encode message.legSide
    ++ (encodeUInt 4 message.legRatio)))))))))

def decode (bytes : List UInt8) : Option (LegInformation × List UInt8) := do
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 6 bytes
  let (legId, bytes) ← decodeUInt 1 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  let (expirationMonth, bytes) ← decodeUInt 1 bytes
  let (expirationDay, bytes) ← decodeUInt 1 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 8 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (legRatio, bytes) ← decodeUInt 4 bytes
  pure ({ optionId, securitySymbol, legId, expirationYear, expirationMonth, expirationDay, explicitStrikePrice, optionType, legSide, legRatio }, bytes)

@[simp] theorem encode_length (message : LegInformation) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, LegSide.encode_length]

theorem encode_length_pos (message : LegInformation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegInformation) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LegInformation

/-- Complex Strategy Directory Message -/
structure ComplexStrategyDirectoryMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  strategyType : StrategyType
  source : BitVec 8
  underlyingSymbol : Alpha 13
  legInformation : Bounded 1 LegInformation
  deriving DecidableEq, Repr

namespace ComplexStrategyDirectoryMessage

def encode (message : ComplexStrategyDirectoryMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (StrategyType.encode message.strategyType
    ++ (encodeUInt 1 message.source
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legInformation.val.length)
    ++ (encodeMany LegInformation.encode message.legInformation.val))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (strategyType, bytes) ← StrategyType.decode bytes
  let (source, bytes) ← decodeUInt 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (legInformation_, bytes) ← decodeMany LegInformation.decode numberOfLegs.toNat bytes
  if fits_legInformation : legInformation_.length < 256 ^ 1 then
    pure ({ timestamp, strategyId, strategyType, source, underlyingSymbol, legInformation := ⟨legInformation_, fits_legInformation⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexStrategyDirectoryMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexStrategyDirectoryMessage) : (encode message).length ≤ 7166 := by
  have bound_legInformation := message.legInformation.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, StrategyType.encode_length, Alpha.encode_length, encodeMany_length_const LegInformation.encode 28 LegInformation.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexStrategyDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StrategyType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegInformation.encode LegInformation.decode LegInformation.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legInformation.length_lt]
  rfl

end ComplexStrategyDirectoryMessage

/-- Strategy Trading Action Message: 11 bytes -/
structure StrategyTradingActionMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace StrategyTradingActionMessage

def encode (message : StrategyTradingActionMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (CurrentTradingState.encode message.currentTradingState))

def decode (bytes : List UInt8) : Option (StrategyTradingActionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ timestamp, strategyId, currentTradingState }, bytes)

@[simp] theorem encode_length (message : StrategyTradingActionMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : StrategyTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CurrentTradingState.decode_encode, some_bind]
  rfl

end StrategyTradingActionMessage

/-- Strategy Open Closed Message: 11 bytes -/
structure StrategyOpenClosedMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  openState : OpenState
  deriving DecidableEq, Repr

namespace StrategyOpenClosedMessage

def encode (message : StrategyOpenClosedMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (OpenState.encode message.openState))

def decode (bytes : List UInt8) : Option (StrategyOpenClosedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (openState, bytes) ← OpenState.decode bytes
  pure ({ timestamp, strategyId, openState }, bytes)

@[simp] theorem encode_length (message : StrategyOpenClosedMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OpenState.encode_length]

theorem encode_length_pos (message : StrategyOpenClosedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyOpenClosedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OpenState.decode_encode, some_bind]
  rfl

end StrategyOpenClosedMessage

/-- Complex Strategy Order On Book Message: 41 bytes -/
structure ComplexStrategyOrderOnBookMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  orderType : OrderType
  side : Side
  price : BitVec 32
  size : BitVec 32
  execFlag : ExecFlag
  orderCapacity : OrderCapacity
  scope : Scope
  ownerId : Alpha 6
  giveup : Alpha 6
  cmta : Alpha 6
  deriving DecidableEq, Repr

namespace ComplexStrategyOrderOnBookMessage

def encode (message : ComplexStrategyOrderOnBookMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (OrderType.encode message.orderType
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.size
    ++ (ExecFlag.encode message.execFlag
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (Scope.encode message.scope
    ++ (Alpha.encode message.ownerId
    ++ (Alpha.encode message.giveup
    ++ (Alpha.encode message.cmta)))))))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyOrderOnBookMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (size, bytes) ← decodeUInt 4 bytes
  let (execFlag, bytes) ← ExecFlag.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (scope, bytes) ← Scope.decode bytes
  let (ownerId, bytes) ← Alpha.decode 6 bytes
  let (giveup, bytes) ← Alpha.decode 6 bytes
  let (cmta, bytes) ← Alpha.decode 6 bytes
  pure ({ timestamp, strategyId, orderType, side, price, size, execFlag, orderCapacity, scope, ownerId, giveup, cmta }, bytes)

@[simp] theorem encode_length (message : ComplexStrategyOrderOnBookMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OrderType.encode_length, Side.encode_length, ExecFlag.encode_length, OrderCapacity.encode_length, Scope.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ComplexStrategyOrderOnBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexStrategyOrderOnBookMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Scope.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexStrategyOrderOnBookMessage

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

/-- Complex Strategy Auction Message -/
structure ComplexStrategyAuctionMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  auctionId : BitVec 32
  orderType : OrderType
  side : Side
  price : BitVec 32
  size : BitVec 32
  execFlag : ExecFlag
  orderCapacity : OrderCapacity
  scope : Scope
  ownerId : Alpha 6
  giveup : Alpha 6
  cmta : Alpha 6
  auctionEvent : AuctionEvent
  auctionType : AuctionType
  auctionResponse : Bounded 1 AuctionResponse
  deriving DecidableEq, Repr

namespace ComplexStrategyAuctionMessage

def encode (message : ComplexStrategyAuctionMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 4 message.auctionId
    ++ (OrderType.encode message.orderType
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.size
    ++ (ExecFlag.encode message.execFlag
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (Scope.encode message.scope
    ++ (Alpha.encode message.ownerId
    ++ (Alpha.encode message.giveup
    ++ (Alpha.encode message.cmta
    ++ (AuctionEvent.encode message.auctionEvent
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.auctionResponse.val.length)
    ++ (encodeMany AuctionResponse.encode message.auctionResponse.val))))))))))))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyAuctionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (size, bytes) ← decodeUInt 4 bytes
  let (execFlag, bytes) ← ExecFlag.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (scope, bytes) ← Scope.decode bytes
  let (ownerId, bytes) ← Alpha.decode 6 bytes
  let (giveup, bytes) ← Alpha.decode 6 bytes
  let (cmta, bytes) ← Alpha.decode 6 bytes
  let (auctionEvent, bytes) ← AuctionEvent.decode bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (numberOfResponses, bytes) ← decodeUInt 1 bytes
  let (auctionResponse_, bytes) ← decodeMany AuctionResponse.decode numberOfResponses.toNat bytes
  if fits_auctionResponse : auctionResponse_.length < 256 ^ 1 then
    pure ({ timestamp, strategyId, auctionId, orderType, side, price, size, execFlag, orderCapacity, scope, ownerId, giveup, cmta, auctionEvent, auctionType, auctionResponse := ⟨auctionResponse_, fits_auctionResponse⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexStrategyAuctionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexStrategyAuctionMessage) : (encode message).length ≤ 2088 := by
  have bound_auctionResponse := message.auctionResponse.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderType.encode_length, Side.encode_length, ExecFlag.encode_length, OrderCapacity.encode_length, Scope.encode_length, Alpha.encode_length, AuctionEvent.encode_length, AuctionType.encode_length, encodeMany_length_const AuctionResponse.encode 8 AuctionResponse.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexStrategyAuctionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Scope.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionEvent.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 AuctionResponse.encode AuctionResponse.decode AuctionResponse.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.auctionResponse.length_lt]
  rfl

end ComplexStrategyAuctionMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | complexStrategyDirectoryMessage (message : ComplexStrategyDirectoryMessage) -- "R" 0x52
  | strategyTradingActionMessage (message : StrategyTradingActionMessage) -- "H" 0x48
  | strategyOpenClosedMessage (message : StrategyOpenClosedMessage) -- "O" 0x4F
  | complexStrategyOrderOnBookMessage (message : ComplexStrategyOrderOnBookMessage) -- "L" 0x4C
  | complexStrategyAuctionMessage (message : ComplexStrategyAuctionMessage) -- "J" 0x4A
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .complexStrategyDirectoryMessage _ => 82
  | .strategyTradingActionMessage _ => 72
  | .strategyOpenClosedMessage _ => 79
  | .complexStrategyOrderOnBookMessage _ => 76
  | .complexStrategyAuctionMessage _ => 74

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .complexStrategyDirectoryMessage message => ComplexStrategyDirectoryMessage.encode message
  | .strategyTradingActionMessage message => StrategyTradingActionMessage.encode message
  | .strategyOpenClosedMessage message => StrategyOpenClosedMessage.encode message
  | .complexStrategyOrderOnBookMessage message => ComplexStrategyOrderOnBookMessage.encode message
  | .complexStrategyAuctionMessage message => ComplexStrategyAuctionMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 7166 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | complexStrategyDirectoryMessage inner =>
    have bound_inner := ComplexStrategyDirectoryMessage.encode_length_le inner
    simp only [encode]
    omega
  | strategyTradingActionMessage inner =>
    simp only [encode, StrategyTradingActionMessage.encode_length]
    omega
  | strategyOpenClosedMessage inner =>
    simp only [encode, StrategyOpenClosedMessage.encode_length]
    omega
  | complexStrategyOrderOnBookMessage inner =>
    simp only [encode, ComplexStrategyOrderOnBookMessage.encode_length]
    omega
  | complexStrategyAuctionMessage inner =>
    have bound_inner := ComplexStrategyAuctionMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (ComplexStrategyDirectoryMessage.decode bytes).map fun (message, rest) => (.complexStrategyDirectoryMessage message, rest)
  else if tag = 72 then (StrategyTradingActionMessage.decode bytes).map fun (message, rest) => (.strategyTradingActionMessage message, rest)
  else if tag = 79 then (StrategyOpenClosedMessage.decode bytes).map fun (message, rest) => (.strategyOpenClosedMessage message, rest)
  else if tag = 76 then (ComplexStrategyOrderOnBookMessage.decode bytes).map fun (message, rest) => (.complexStrategyOrderOnBookMessage message, rest)
  else if tag = 74 then (ComplexStrategyAuctionMessage.decode bytes).map fun (message, rest) => (.complexStrategyAuctionMessage message, rest)
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
  | complexStrategyDirectoryMessage inner =>
    have bound_inner := ComplexStrategyDirectoryMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUInt_length]
    omega
  | strategyTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StrategyTradingActionMessage.encode_length]
    omega
  | strategyOpenClosedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StrategyOpenClosedMessage.encode_length]
    omega
  | complexStrategyOrderOnBookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ComplexStrategyOrderOnBookMessage.encode_length]
    omega
  | complexStrategyAuctionMessage inner =>
    have bound_inner := ComplexStrategyAuctionMessage.encode_length_le inner
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

end Omi.NasdaqIseoptionsOrdercombofeedItchV11
