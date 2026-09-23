import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Spread Orders v2.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqPhlxoptionsSpreadordersItchV21Server

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
  [0x56, 0x54, 0x44, 0x53, 0x47, 0x43, 0x52, 0x41, 0x42, 0x46, 0x55]

inductive StrategyType where
  | verticalSpread -- Vertical Spread
  | timeSpread -- Time Spread
  | diagonalSpread -- Diagonal Spread
  | straddle -- Straddle
  | strangle -- Strangle
  | combo -- Combo
  | riskReversal -- Risk Reversal
  | ratioSpread -- Ratio Spread
  | boxSpread -- Box Spread
  | butterflySpread -- Butterfly Spread
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
  | .boxSpread => 0x42
  | .butterflySpread => 0x46
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
  else if byte = 0x42 then .boxSpread
  else if byte = 0x46 then .butterflySpread
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
  | boxSpread => decide
  | butterflySpread => decide
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
  | callOption -- Call Option
  | putOption -- Put Option
  | stockLeg -- Stock Leg
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .callOption => 0x43
  | .putOption => 0x50
  | .stockLeg => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .callOption
  else if byte = 0x50 then .putOption
  else .stockLeg

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | callOption => decide
  | putOption => decide
  | stockLeg => decide
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

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x48, 0x54, 0x49, 0x4F, 0x52, 0x58]

inductive CurrentTradingState where
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
  | .haltInEffect => 0x48
  | .continuousTrading => 0x54
  | .preOpen => 0x49
  | .openingAuction => 0x4F
  | .reOpening => 0x52
  | .closed => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .haltInEffect
  else if byte = 0x54 then .continuousTrading
  else if byte = 0x49 then .preOpen
  else if byte = 0x4F then .openingAuction
  else if byte = 0x52 then .reOpening
  else .closed

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
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
  [0x43, 0x46, 0x4D, 0x42, 0x50, 0x4F, 0x4A]

inductive OrderCapacity where
  | customerOrder -- Customer Order
  | firmOrder -- Firm Order
  | nasdaqRegisteredMarketMaker -- Nasdaq Registered Market Maker
  | brokerDealerOder -- Broker Dealer Oder
  | professionalOrder -- Professional Order
  | otherExchangeRegisteredMarketMaker -- Other Exchange Registered Market Maker
  | jboJointBackOfficeOnlyPhlx -- Jbo Joint Back Office Only Phlx
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderCapacity

def toByte : OrderCapacity → UInt8
  | .customerOrder => 0x43
  | .firmOrder => 0x46
  | .nasdaqRegisteredMarketMaker => 0x4D
  | .brokerDealerOder => 0x42
  | .professionalOrder => 0x50
  | .otherExchangeRegisteredMarketMaker => 0x4F
  | .jboJointBackOfficeOnlyPhlx => 0x4A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderCapacity :=
  if byte = 0x43 then .customerOrder
  else if byte = 0x46 then .firmOrder
  else if byte = 0x4D then .nasdaqRegisteredMarketMaker
  else if byte = 0x42 then .brokerDealerOder
  else if byte = 0x50 then .professionalOrder
  else if byte = 0x4F then .otherExchangeRegisteredMarketMaker
  else .jboJointBackOfficeOnlyPhlx

def ofByte (byte : UInt8) : OrderCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderCapacity) : ofByte value.toByte = value := by
  cases value with
  | customerOrder => decide
  | firmOrder => decide
  | nasdaqRegisteredMarketMaker => decide
  | brokerDealerOder => decide
  | professionalOrder => decide
  | otherExchangeRegisteredMarketMaker => decide
  | jboJointBackOfficeOnlyPhlx => decide
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

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x45, 0x50, 0x43, 0x53, 0x58]

inductive AuctionType where
  | complexExposure -- Complex Exposure
  | priceImprovementPimAuction -- Price Improvement Pim Auction
  | facilitation -- Facilitation
  | solicitation -- Solicitation
  | flexAuction -- Flex Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .complexExposure => 0x45
  | .priceImprovementPimAuction => 0x50
  | .facilitation => 0x43
  | .solicitation => 0x53
  | .flexAuction => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x45 then .complexExposure
  else if byte = 0x50 then .priceImprovementPimAuction
  else if byte = 0x43 then .facilitation
  else if byte = 0x53 then .solicitation
  else .flexAuction

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | complexExposure => decide
  | priceImprovementPimAuction => decide
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

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  text : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (text, bytes) ← Alpha.decode 1 bytes
  pure ({ text }, bytes)

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

/-- Leg Information: 25 bytes -/
structure LegInformation where
  optionId : BitVec 32
  securitySymbol : Alpha 8
  expirationYear : BitVec 8
  expirationMonth : BitVec 8
  expirationDay : BitVec 8
  explicitStrikePrice : BitVec 32
  optionType : OptionType
  side : Side
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace LegInformation

def encode (message : LegInformation) : List UInt8 :=
  encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 1 message.expirationYear
    ++ (encodeUInt 1 message.expirationMonth
    ++ (encodeUInt 1 message.expirationDay
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.legRatio))))))))

def decode (bytes : List UInt8) : Option (LegInformation × List UInt8) := do
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 8 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  let (expirationMonth, bytes) ← decodeUInt 1 bytes
  let (expirationDay, bytes) ← decodeUInt 1 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (legRatio, bytes) ← decodeUInt 4 bytes
  pure ({ optionId, securitySymbol, expirationYear, expirationMonth, expirationDay, explicitStrikePrice, optionType, side, legRatio }, bytes)

@[simp] theorem encode_length (message : LegInformation) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, Side.encode_length]

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
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LegInformation

/-- Complex Strategy Directory Message -/
structure ComplexStrategyDirectoryMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  strategyId : BitVec 32
  strategyType : StrategyType
  underlyingSymbol : Alpha 13
  reserved16 : Alpha 16
  legInformation : Bounded 1 LegInformation
  deriving DecidableEq, Repr

namespace ComplexStrategyDirectoryMessage

def encode (message : ComplexStrategyDirectoryMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (StrategyType.encode message.strategyType
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.reserved16
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legInformation.val.length)
    ++ (encodeMany LegInformation.encode message.legInformation.val)))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyDirectoryMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (strategyType, bytes) ← StrategyType.decode bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (legInformation_, bytes) ← decodeMany LegInformation.decode numberOfLegs.toNat bytes
  if fits_legInformation : legInformation_.length < 256 ^ 1 then
    pure ({ trackingNumber, timestamp, strategyId, strategyType, underlyingSymbol, reserved16, legInformation := ⟨legInformation_, fits_legInformation⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexStrategyDirectoryMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexStrategyDirectoryMessage) : (encode message).length ≤ 6420 := by
  have bound_legInformation := message.legInformation.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, StrategyType.encode_length, Alpha.encode_length, encodeMany_length_const LegInformation.encode 25 LegInformation.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexStrategyDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StrategyType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

/-- Strategy Trading Action Message: 15 bytes -/
structure StrategyTradingActionMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  strategyId : BitVec 32
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace StrategyTradingActionMessage

def encode (message : StrategyTradingActionMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (CurrentTradingState.encode message.currentTradingState)))

def decode (bytes : List UInt8) : Option (StrategyTradingActionMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ trackingNumber, timestamp, strategyId, currentTradingState }, bytes)

@[simp] theorem encode_length (message : StrategyTradingActionMessage) : (encode message).length = 15 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CurrentTradingState.decode_encode, some_bind]
  rfl

end StrategyTradingActionMessage

/-- Complex Add Order Message: 58 bytes -/
structure ComplexAddOrderMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  strategyId : BitVec 32
  orderReferenceNumber : BitVec 64
  side : Side
  originalOrderVolume : BitVec 32
  executableOrderVolume : BitVec 32
  orderStatus : OrderStatus
  orderType : OrderType
  limitPrice : BitVec 32
  timeInForce : TimeInForce
  orderCapacity : OrderCapacity
  scope : Scope
  ownerId : Alpha 6
  giveup : Alpha 6
  cmta : Alpha 6
  deriving DecidableEq, Repr

namespace ComplexAddOrderMessage

def encode (message : ComplexAddOrderMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.originalOrderVolume
    ++ (encodeUInt 4 message.executableOrderVolume
    ++ (OrderStatus.encode message.orderStatus
    ++ (OrderType.encode message.orderType
    ++ (encodeUInt 4 message.limitPrice
    ++ (TimeInForce.encode message.timeInForce
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (Scope.encode message.scope
    ++ (Alpha.encode message.ownerId
    ++ (Alpha.encode message.giveup
    ++ (Alpha.encode message.cmta)))))))))))))))

def decode (bytes : List UInt8) : Option (ComplexAddOrderMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (originalOrderVolume, bytes) ← decodeUInt 4 bytes
  let (executableOrderVolume, bytes) ← decodeUInt 4 bytes
  let (orderStatus, bytes) ← OrderStatus.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (limitPrice, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (scope, bytes) ← Scope.decode bytes
  let (ownerId, bytes) ← Alpha.decode 6 bytes
  let (giveup, bytes) ← Alpha.decode 6 bytes
  let (cmta, bytes) ← Alpha.decode 6 bytes
  pure ({ trackingNumber, timestamp, strategyId, orderReferenceNumber, side, originalOrderVolume, executableOrderVolume, orderStatus, orderType, limitPrice, timeInForce, orderCapacity, scope, ownerId, giveup, cmta }, bytes)

@[simp] theorem encode_length (message : ComplexAddOrderMessage) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, OrderStatus.encode_length, OrderType.encode_length, TimeInForce.encode_length, OrderCapacity.encode_length, Scope.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ComplexAddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexAddOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
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

end ComplexAddOrderMessage

/-- Flex Dac Leg Information: 8 bytes -/
structure FlexDacLegInformation where
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace FlexDacLegInformation

def encode (message : FlexDacLegInformation) : List UInt8 :=
  Alpha.encode message.reserved8

def decode (bytes : List UInt8) : Option (FlexDacLegInformation × List UInt8) := do
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ reserved8 }, bytes)

@[simp] theorem encode_length (message : FlexDacLegInformation) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : FlexDacLegInformation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FlexDacLegInformation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end FlexDacLegInformation

/-- Complex Strategy Auction Message -/
structure ComplexStrategyAuctionMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  strategyId : BitVec 32
  auctionId : BitVec 32
  auctionType : AuctionType
  auctionDuration : BitVec 32
  auctionEvent : AuctionEvent
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
  responsePrice : BitVec 32
  responseSize : BitVec 32
  reserved4 : Alpha 4
  flexDacLegInformation : Bounded 1 FlexDacLegInformation
  deriving DecidableEq, Repr

namespace ComplexStrategyAuctionMessage

def encode (message : ComplexStrategyAuctionMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 4 message.auctionId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.auctionDuration
    ++ (AuctionEvent.encode message.auctionEvent
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
    ++ (encodeUInt 4 message.responsePrice
    ++ (encodeUInt 4 message.responseSize
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.flexDacLegInformation.val.length)
    ++ (encodeMany FlexDacLegInformation.encode message.flexDacLegInformation.val)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyAuctionMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (auctionDuration, bytes) ← decodeUInt 4 bytes
  let (auctionEvent, bytes) ← AuctionEvent.decode bytes
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
  let (responsePrice, bytes) ← decodeUInt 4 bytes
  let (responseSize, bytes) ← decodeUInt 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (numberOfFlexDacLegs, bytes) ← decodeUInt 1 bytes
  let (flexDacLegInformation_, bytes) ← decodeMany FlexDacLegInformation.decode numberOfFlexDacLegs.toNat bytes
  if fits_flexDacLegInformation : flexDacLegInformation_.length < 256 ^ 1 then
    pure ({ trackingNumber, timestamp, strategyId, auctionId, auctionType, auctionDuration, auctionEvent, orderType, side, price, size, execFlag, orderCapacity, scope, ownerId, giveup, cmta, responsePrice, responseSize, reserved4, flexDacLegInformation := ⟨flexDacLegInformation_, fits_flexDacLegInformation⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexStrategyAuctionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexStrategyAuctionMessage) : (encode message).length ≤ 2108 := by
  have bound_flexDacLegInformation := message.flexDacLegInformation.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, AuctionType.encode_length, AuctionEvent.encode_length, OrderType.encode_length, Side.encode_length, ExecFlag.encode_length, OrderCapacity.encode_length, Scope.encode_length, Alpha.encode_length, encodeMany_length_const FlexDacLegInformation.encode 8 FlexDacLegInformation.encode_length]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionEvent.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 FlexDacLegInformation.encode FlexDacLegInformation.decode FlexDacLegInformation.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.flexDacLegInformation.length_lt]
  rfl

end ComplexStrategyAuctionMessage

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
  | complexStrategyDirectoryMessage (message : ComplexStrategyDirectoryMessage) -- "s" 0x73
  | strategyTradingActionMessage (message : StrategyTradingActionMessage) -- "H" 0x48
  | complexAddOrderMessage (message : ComplexAddOrderMessage) -- "C" 0x43
  | complexStrategyAuctionMessage (message : ComplexStrategyAuctionMessage) -- "a" 0x61
  | endOfReplaySequenceMessage (message : EndOfReplaySequenceMessage) -- "M" 0x4D
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .complexStrategyDirectoryMessage _ => 115
  | .strategyTradingActionMessage _ => 72
  | .complexAddOrderMessage _ => 67
  | .complexStrategyAuctionMessage _ => 97
  | .endOfReplaySequenceMessage _ => 77

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .complexStrategyDirectoryMessage message => ComplexStrategyDirectoryMessage.encode message
  | .strategyTradingActionMessage message => StrategyTradingActionMessage.encode message
  | .complexAddOrderMessage message => ComplexAddOrderMessage.encode message
  | .complexStrategyAuctionMessage message => ComplexStrategyAuctionMessage.encode message
  | .endOfReplaySequenceMessage message => EndOfReplaySequenceMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 6420 := by
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
  | complexAddOrderMessage inner =>
    simp only [encode, ComplexAddOrderMessage.encode_length]
    omega
  | complexStrategyAuctionMessage inner =>
    have bound_inner := ComplexStrategyAuctionMessage.encode_length_le inner
    simp only [encode]
    omega
  | endOfReplaySequenceMessage inner =>
    simp only [encode, EndOfReplaySequenceMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 115 then (ComplexStrategyDirectoryMessage.decode bytes).map fun (message, rest) => (.complexStrategyDirectoryMessage message, rest)
  else if tag = 72 then (StrategyTradingActionMessage.decode bytes).map fun (message, rest) => (.strategyTradingActionMessage message, rest)
  else if tag = 67 then (ComplexAddOrderMessage.decode bytes).map fun (message, rest) => (.complexAddOrderMessage message, rest)
  else if tag = 97 then (ComplexStrategyAuctionMessage.decode bytes).map fun (message, rest) => (.complexStrategyAuctionMessage message, rest)
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
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 6421 := by
  unfold encode
  cases message.sequencedMessage with
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | complexStrategyDirectoryMessage inner =>
    have bound_inner := ComplexStrategyDirectoryMessage.encode_length_le inner
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | strategyTradingActionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, StrategyTradingActionMessage.encode_length]
    omega
  | complexAddOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ComplexAddOrderMessage.encode_length]
    omega
  | complexStrategyAuctionMessage inner =>
    have bound_inner := ComplexStrategyAuctionMessage.encode_length_le inner
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length]
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
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 6421 := by
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

end Omi.NasdaqPhlxoptionsSpreadordersItchV21Server
