import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Depth Of Market v2.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqMrxoptionsDepthofmarketItchV21Server

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
  [0x42, 0x53, 0x4D, 0x4E]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | buyImplied -- Buy Implied
  | sellImplied -- Sell Implied
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .buyImplied => 0x4D
  | .sellImplied => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x4D then .buyImplied
  else .sellImplied

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | buyImplied => decide
  | sellImplied => decide
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

/-- Printable: one byte code -/
def Printable.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Printable where
  | nonPrintable -- Non Printable
  | printable -- Printable
  | unlisted (byte : { byte : UInt8 // byte ∉ Printable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Printable

def toByte : Printable → UInt8
  | .nonPrintable => 0x4E
  | .printable => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Printable :=
  if byte = 0x4E then .nonPrintable
  else .printable

def ofByte (byte : UInt8) : Printable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Printable) : ofByte value.toByte = value := by
  cases value with
  | nonPrintable => decide
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
  [0x42, 0x4F, 0x52, 0x50, 0x43, 0x53, 0x58, 0x4E, 0x45]

inductive CrossType where
  | blockAuction -- Block Auction
  | openingAuction -- Opening Auction
  | reOpeningAuction -- Re Opening Auction
  | priceImprovementAuction -- Price Improvement Auction
  | facilitation -- Facilitation
  | solicitation -- Solicitation
  | flexAuction -- Flex Auction
  | none_ -- None
  | complexExposureAuction -- Complex Exposure Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .blockAuction => 0x42
  | .openingAuction => 0x4F
  | .reOpeningAuction => 0x52
  | .priceImprovementAuction => 0x50
  | .facilitation => 0x43
  | .solicitation => 0x53
  | .flexAuction => 0x58
  | .none_ => 0x4E
  | .complexExposureAuction => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x42 then .blockAuction
  else if byte = 0x4F then .openingAuction
  else if byte = 0x52 then .reOpeningAuction
  else if byte = 0x50 then .priceImprovementAuction
  else if byte = 0x43 then .facilitation
  else if byte = 0x53 then .solicitation
  else if byte = 0x58 then .flexAuction
  else if byte = 0x4E then .none_
  else .complexExposureAuction

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | blockAuction => decide
  | openingAuction => decide
  | reOpeningAuction => decide
  | priceImprovementAuction => decide
  | facilitation => decide
  | solicitation => decide
  | flexAuction => decide
  | none_ => decide
  | complexExposureAuction => decide
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
  [0x4F, 0x52, 0x50, 0x49, 0x42]

inductive AuctionType where
  | opening -- Opening
  | reopening -- Reopening
  | priceImprovementAuction -- Price Improvement Auction
  | orderExposure -- Order Exposure
  | blockAuction -- Block Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .opening => 0x4F
  | .reopening => 0x52
  | .priceImprovementAuction => 0x50
  | .orderExposure => 0x49
  | .blockAuction => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x4F then .opening
  else if byte = 0x52 then .reopening
  else if byte = 0x50 then .priceImprovementAuction
  else if byte = 0x49 then .orderExposure
  else .blockAuction

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | opening => decide
  | reopening => decide
  | priceImprovementAuction => decide
  | orderExposure => decide
  | blockAuction => decide
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

/-- Side Imbalance Direction: one byte code -/
def SideImbalanceDirection.codes : List UInt8 :=
  [0x42, 0x53]

inductive SideImbalanceDirection where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ SideImbalanceDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SideImbalanceDirection

def toByte : SideImbalanceDirection → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SideImbalanceDirection :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : SideImbalanceDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SideImbalanceDirection) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SideImbalanceDirection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SideImbalanceDirection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SideImbalanceDirection) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SideImbalanceDirection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SideImbalanceDirection

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

/-- Add Order Short Form Message: 32 bytes -/
structure AddOrderShortFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderReferenceNumber : BitVec 64
  side : Side
  orderCapacity : OrderCapacity
  priceShort : BitVec 16
  volumeShort : BitVec 16
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace AddOrderShortFormMessage

def encode (message : AddOrderShortFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (encodeUInt 2 message.priceShort
    ++ (encodeUInt 2 message.volumeShort
    ++ (Alpha.encode message.reserved4))))))))

def decode (bytes : List UInt8) : Option (AddOrderShortFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (priceShort, bytes) ← decodeUInt 2 bytes
  let (volumeShort, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, orderReferenceNumber, side, orderCapacity, priceShort, volumeShort, reserved4 }, bytes)

@[simp] theorem encode_length (message : AddOrderShortFormMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, OrderCapacity.encode_length, Alpha.encode_length]

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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderShortFormMessage

/-- Add Order Long Form Message: 36 bytes -/
structure AddOrderLongFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderReferenceNumber : BitVec 64
  side : Side
  orderCapacity : OrderCapacity
  priceLong : BitVec 32
  volumeLong : BitVec 32
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace AddOrderLongFormMessage

def encode (message : AddOrderLongFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong
    ++ (Alpha.encode message.reserved4))))))))

def decode (bytes : List UInt8) : Option (AddOrderLongFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, orderReferenceNumber, side, orderCapacity, priceLong, volumeLong, reserved4 }, bytes)

@[simp] theorem encode_length (message : AddOrderLongFormMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, OrderCapacity.encode_length, Alpha.encode_length]

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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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

/-- Single Side Executed Message: 43 bytes -/
structure SingleSideExecutedMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  strategyId : BitVec 32
  orderReferenceNumber : BitVec 64
  executedVolume : BitVec 32
  tradeCondition : Alpha 1
  auctionId : BitVec 32
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideExecutedMessage

def encode (message : SingleSideExecutedMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeUInt 4 message.executedVolume
    ++ (Alpha.encode message.tradeCondition
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber)))))))))

def decode (bytes : List UInt8) : Option (SingleSideExecutedMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (executedVolume, bytes) ← decodeUInt 4 bytes
  let (tradeCondition, bytes) ← Alpha.decode 1 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, strategyId, orderReferenceNumber, executedVolume, tradeCondition, auctionId, crossNumber, matchNumber }, bytes)

@[simp] theorem encode_length (message : SingleSideExecutedMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleSideExecutedMessage

/-- Single Side Executed With Price Message: 48 bytes -/
structure SingleSideExecutedWithPriceMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  strategyId : BitVec 32
  orderReferenceNumber : BitVec 64
  crossNumber : BitVec 32
  matchNumber : BitVec 32
  printable : Printable
  priceLong : BitVec 32
  volumeLong : BitVec 32
  tradeCondition : Alpha 1
  auctionId : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideExecutedWithPriceMessage

def encode (message : SingleSideExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeUInt 4 message.crossNumber
    ++ (encodeUInt 4 message.matchNumber
    ++ (Printable.encode message.printable
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong
    ++ (Alpha.encode message.tradeCondition
    ++ (encodeUInt 4 message.auctionId)))))))))))

def decode (bytes : List UInt8) : Option (SingleSideExecutedWithPriceMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (crossNumber, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  let (tradeCondition, bytes) ← Alpha.decode 1 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, strategyId, orderReferenceNumber, crossNumber, matchNumber, printable := printable_, priceLong, volumeLong, tradeCondition, auctionId }, bytes)

@[simp] theorem encode_length (message : SingleSideExecutedWithPriceMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length, Alpha.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleSideExecutedWithPriceMessage

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

/-- Single Side Replace Short Form Message: 34 bytes -/
structure SingleSideReplaceShortFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderReferenceNumber : BitVec 64
  newReferenceNumber : BitVec 64
  priceShort : BitVec 16
  volumeShort : BitVec 16
  deriving DecidableEq, Repr

namespace SingleSideReplaceShortFormMessage

def encode (message : SingleSideReplaceShortFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeUInt 8 message.newReferenceNumber
    ++ (encodeUInt 2 message.priceShort
    ++ (encodeUInt 2 message.volumeShort))))))

def decode (bytes : List UInt8) : Option (SingleSideReplaceShortFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (newReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (priceShort, bytes) ← decodeUInt 2 bytes
  let (volumeShort, bytes) ← decodeUInt 2 bytes
  pure ({ trackingNumber, timestamp, instrumentId, orderReferenceNumber, newReferenceNumber, priceShort, volumeShort }, bytes)

@[simp] theorem encode_length (message : SingleSideReplaceShortFormMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SingleSideReplaceShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideReplaceShortFormMessage) (rest : List UInt8) :
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

end SingleSideReplaceShortFormMessage

/-- Single Side Replace Long Form Message: 38 bytes -/
structure SingleSideReplaceLongFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderReferenceNumber : BitVec 64
  newReferenceNumber : BitVec 64
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideReplaceLongFormMessage

def encode (message : SingleSideReplaceLongFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeUInt 8 message.newReferenceNumber
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong))))))

def decode (bytes : List UInt8) : Option (SingleSideReplaceLongFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (newReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, orderReferenceNumber, newReferenceNumber, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : SingleSideReplaceLongFormMessage) : (encode message).length = 38 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleSideReplaceLongFormMessage

/-- Single Side Delete Message: 22 bytes -/
structure SingleSideDeleteMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace SingleSideDeleteMessage

def encode (message : SingleSideDeleteMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderReferenceNumber)))

def decode (bytes : List UInt8) : Option (SingleSideDeleteMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ trackingNumber, timestamp, instrumentId, orderReferenceNumber }, bytes)

@[simp] theorem encode_length (message : SingleSideDeleteMessage) : (encode message).length = 22 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SingleSideDeleteMessage

/-- Single Side Update Message: 31 bytes -/
structure SingleSideUpdateMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderReferenceNumber : BitVec 64
  changeReason : ChangeReason
  priceLong : BitVec 32
  volumeLong : BitVec 32
  deriving DecidableEq, Repr

namespace SingleSideUpdateMessage

def encode (message : SingleSideUpdateMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (ChangeReason.encode message.changeReason
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong))))))

def decode (bytes : List UInt8) : Option (SingleSideUpdateMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (changeReason, bytes) ← ChangeReason.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, orderReferenceNumber, changeReason, priceLong, volumeLong }, bytes)

@[simp] theorem encode_length (message : SingleSideUpdateMessage) : (encode message).length = 31 := by
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

/-- Trade Message: 58 bytes -/
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
  tradeCondition : Alpha 1
  auctionId : BitVec 32
  printable : Printable
  tradeType : TradeType
  reserved16 : Alpha 16
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
    ++ (Alpha.encode message.tradeCondition
    ++ (encodeUInt 4 message.auctionId
    ++ (Printable.encode message.printable
    ++ (TradeType.encode message.tradeType
    ++ (Alpha.encode message.reserved16)))))))))))))

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
  let (tradeCondition, bytes) ← Alpha.decode 1 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ trackingNumber, timestamp, instrumentId, crossNumber, matchNumber, strategyId, crossType, priceLong, volumeLong, tradeCondition, auctionId, printable := printable_, tradeType, reserved16 }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CrossType.encode_length, Alpha.encode_length, Printable.encode_length, TradeType.encode_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Net Order Imbalance Message: 33 bytes -/
structure NetOrderImbalanceMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  auctionId : BitVec 32
  auctionType : AuctionType
  pairedQuantity : BitVec 32
  sideImbalanceDirection : SideImbalanceDirection
  priceImbalancePrice : BitVec 32
  imbalanceVolume : BitVec 32
  orderCapacity : OrderCapacity
  deriving DecidableEq, Repr

namespace NetOrderImbalanceMessage

def encode (message : NetOrderImbalanceMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.auctionId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.pairedQuantity
    ++ (SideImbalanceDirection.encode message.sideImbalanceDirection
    ++ (encodeUInt 4 message.priceImbalancePrice
    ++ (encodeUInt 4 message.imbalanceVolume
    ++ (OrderCapacity.encode message.orderCapacity)))))))))

def decode (bytes : List UInt8) : Option (NetOrderImbalanceMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (pairedQuantity, bytes) ← decodeUInt 4 bytes
  let (sideImbalanceDirection, bytes) ← SideImbalanceDirection.decode bytes
  let (priceImbalancePrice, bytes) ← decodeUInt 4 bytes
  let (imbalanceVolume, bytes) ← decodeUInt 4 bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  pure ({ trackingNumber, timestamp, instrumentId, auctionId, auctionType, pairedQuantity, sideImbalanceDirection, priceImbalancePrice, imbalanceVolume, orderCapacity }, bytes)

@[simp] theorem encode_length (message : NetOrderImbalanceMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, AuctionType.encode_length, SideImbalanceDirection.encode_length, OrderCapacity.encode_length]

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
  rw [List.append_assoc, SideImbalanceDirection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OrderCapacity.decode_encode, some_bind]
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
  | derivativeDirectoryMessage (message : DerivativeDirectoryMessage) -- "m" 0x6D
  | tradingActionMessage (message : TradingActionMessage) -- "H" 0x48
  | addOrderShortFormMessage (message : AddOrderShortFormMessage) -- "r" 0x72
  | addOrderLongFormMessage (message : AddOrderLongFormMessage) -- "o" 0x6F
  | addQuoteShortFormMessage (message : AddQuoteShortFormMessage) -- "j" 0x6A
  | addQuoteLongFormMessage (message : AddQuoteLongFormMessage) -- "J" 0x4A
  | singleSideExecutedMessage (message : SingleSideExecutedMessage) -- "e" 0x65
  | singleSideExecutedWithPriceMessage (message : SingleSideExecutedWithPriceMessage) -- "c" 0x63
  | orderCancelMessage (message : OrderCancelMessage) -- "X" 0x58
  | singleSideReplaceShortFormMessage (message : SingleSideReplaceShortFormMessage) -- "u" 0x75
  | singleSideReplaceLongFormMessage (message : SingleSideReplaceLongFormMessage) -- "U" 0x55
  | singleSideDeleteMessage (message : SingleSideDeleteMessage) -- "D" 0x44
  | singleSideUpdateMessage (message : SingleSideUpdateMessage) -- "G" 0x47
  | quoteReplaceShortFormMessage (message : QuoteReplaceShortFormMessage) -- "k" 0x6B
  | quoteReplaceLongFormMessage (message : QuoteReplaceLongFormMessage) -- "K" 0x4B
  | quoteDeleteMessage (message : QuoteDeleteMessage) -- "Y" 0x59
  | tradeMessage (message : TradeMessage) -- "q" 0x71
  | netOrderImbalanceMessage (message : NetOrderImbalanceMessage) -- "O" 0x4F
  | endOfReplaySequenceMessage (message : EndOfReplaySequenceMessage) -- "M" 0x4D
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .derivativeDirectoryMessage _ => 109
  | .tradingActionMessage _ => 72
  | .addOrderShortFormMessage _ => 114
  | .addOrderLongFormMessage _ => 111
  | .addQuoteShortFormMessage _ => 106
  | .addQuoteLongFormMessage _ => 74
  | .singleSideExecutedMessage _ => 101
  | .singleSideExecutedWithPriceMessage _ => 99
  | .orderCancelMessage _ => 88
  | .singleSideReplaceShortFormMessage _ => 117
  | .singleSideReplaceLongFormMessage _ => 85
  | .singleSideDeleteMessage _ => 68
  | .singleSideUpdateMessage _ => 71
  | .quoteReplaceShortFormMessage _ => 107
  | .quoteReplaceLongFormMessage _ => 75
  | .quoteDeleteMessage _ => 89
  | .tradeMessage _ => 113
  | .netOrderImbalanceMessage _ => 79
  | .endOfReplaySequenceMessage _ => 77

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .derivativeDirectoryMessage message => DerivativeDirectoryMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .addOrderShortFormMessage message => AddOrderShortFormMessage.encode message
  | .addOrderLongFormMessage message => AddOrderLongFormMessage.encode message
  | .addQuoteShortFormMessage message => AddQuoteShortFormMessage.encode message
  | .addQuoteLongFormMessage message => AddQuoteLongFormMessage.encode message
  | .singleSideExecutedMessage message => SingleSideExecutedMessage.encode message
  | .singleSideExecutedWithPriceMessage message => SingleSideExecutedWithPriceMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .singleSideReplaceShortFormMessage message => SingleSideReplaceShortFormMessage.encode message
  | .singleSideReplaceLongFormMessage message => SingleSideReplaceLongFormMessage.encode message
  | .singleSideDeleteMessage message => SingleSideDeleteMessage.encode message
  | .singleSideUpdateMessage message => SingleSideUpdateMessage.encode message
  | .quoteReplaceShortFormMessage message => QuoteReplaceShortFormMessage.encode message
  | .quoteReplaceLongFormMessage message => QuoteReplaceLongFormMessage.encode message
  | .quoteDeleteMessage message => QuoteDeleteMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .netOrderImbalanceMessage message => NetOrderImbalanceMessage.encode message
  | .endOfReplaySequenceMessage message => EndOfReplaySequenceMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 62 := by
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
  | singleSideExecutedMessage inner =>
    simp only [encode, SingleSideExecutedMessage.encode_length]
    omega
  | singleSideExecutedWithPriceMessage inner =>
    simp only [encode, SingleSideExecutedWithPriceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [encode, OrderCancelMessage.encode_length]
    omega
  | singleSideReplaceShortFormMessage inner =>
    simp only [encode, SingleSideReplaceShortFormMessage.encode_length]
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
  else if tag = 109 then (DerivativeDirectoryMessage.decode bytes).map fun (message, rest) => (.derivativeDirectoryMessage message, rest)
  else if tag = 72 then (TradingActionMessage.decode bytes).map fun (message, rest) => (.tradingActionMessage message, rest)
  else if tag = 114 then (AddOrderShortFormMessage.decode bytes).map fun (message, rest) => (.addOrderShortFormMessage message, rest)
  else if tag = 111 then (AddOrderLongFormMessage.decode bytes).map fun (message, rest) => (.addOrderLongFormMessage message, rest)
  else if tag = 106 then (AddQuoteShortFormMessage.decode bytes).map fun (message, rest) => (.addQuoteShortFormMessage message, rest)
  else if tag = 74 then (AddQuoteLongFormMessage.decode bytes).map fun (message, rest) => (.addQuoteLongFormMessage message, rest)
  else if tag = 101 then (SingleSideExecutedMessage.decode bytes).map fun (message, rest) => (.singleSideExecutedMessage message, rest)
  else if tag = 99 then (SingleSideExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.singleSideExecutedWithPriceMessage message, rest)
  else if tag = 88 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 117 then (SingleSideReplaceShortFormMessage.decode bytes).map fun (message, rest) => (.singleSideReplaceShortFormMessage message, rest)
  else if tag = 85 then (SingleSideReplaceLongFormMessage.decode bytes).map fun (message, rest) => (.singleSideReplaceLongFormMessage message, rest)
  else if tag = 68 then (SingleSideDeleteMessage.decode bytes).map fun (message, rest) => (.singleSideDeleteMessage message, rest)
  else if tag = 71 then (SingleSideUpdateMessage.decode bytes).map fun (message, rest) => (.singleSideUpdateMessage message, rest)
  else if tag = 107 then (QuoteReplaceShortFormMessage.decode bytes).map fun (message, rest) => (.quoteReplaceShortFormMessage message, rest)
  else if tag = 75 then (QuoteReplaceLongFormMessage.decode bytes).map fun (message, rest) => (.quoteReplaceLongFormMessage message, rest)
  else if tag = 89 then (QuoteDeleteMessage.decode bytes).map fun (message, rest) => (.quoteDeleteMessage message, rest)
  else if tag = 113 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 79 then (NetOrderImbalanceMessage.decode bytes).map fun (message, rest) => (.netOrderImbalanceMessage message, rest)
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
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 63 := by
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
  | singleSideExecutedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SingleSideExecutedMessage.encode_length]
    omega
  | singleSideExecutedWithPriceMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SingleSideExecutedWithPriceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderCancelMessage.encode_length]
    omega
  | singleSideReplaceShortFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SingleSideReplaceShortFormMessage.encode_length]
    omega
  | singleSideReplaceLongFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SingleSideReplaceLongFormMessage.encode_length]
    omega
  | singleSideDeleteMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SingleSideDeleteMessage.encode_length]
    omega
  | singleSideUpdateMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SingleSideUpdateMessage.encode_length]
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
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 63 := by
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

end Omi.NasdaqMrxoptionsDepthofmarketItchV21Server
