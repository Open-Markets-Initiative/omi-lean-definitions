import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Clearing Trade Interface v3.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqGemxoptionsCtiItchV30Server

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

/-- Option Kind: one byte code -/
def OptionKind.codes : List UInt8 :=
  [0x43, 0x50, 0x20]

inductive OptionKind where
  | call -- Call
  | put -- Put
  | stockLeg -- Stock Leg
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionKind.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionKind

def toByte : OptionKind → UInt8
  | .call => 0x43
  | .put => 0x50
  | .stockLeg => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionKind :=
  if byte = 0x43 then .call
  else if byte = 0x50 then .put
  else .stockLeg

def ofByte (byte : UInt8) : OptionKind :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionKind) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | stockLeg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionKind) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionKind × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionKind) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionKind) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionKind

/-- Option Closing Type: one byte code -/
def OptionClosingType.codes : List UInt8 :=
  [0x4E, 0x4C]

inductive OptionClosingType where
  | normalHours -- Normal Hours
  | lateHours -- Late Hours
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionClosingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionClosingType

def toByte : OptionClosingType → UInt8
  | .normalHours => 0x4E
  | .lateHours => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionClosingType :=
  if byte = 0x4E then .normalHours
  else .lateHours

def ofByte (byte : UInt8) : OptionClosingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionClosingType) : ofByte value.toByte = value := by
  cases value with
  | normalHours => decide
  | lateHours => decide
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
  | nonTradable -- Non Tradable
  | unlisted (byte : { byte : UInt8 // byte ∉ Tradable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tradable

def toByte : Tradable → UInt8
  | .tradable => 0x59
  | .nonTradable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tradable :=
  if byte = 0x59 then .tradable
  else .nonTradable

def ofByte (byte : UInt8) : Tradable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tradable) : ofByte value.toByte = value := by
  cases value with
  | tradable => decide
  | nonTradable => decide
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

/-- Send Type: one byte code -/
def SendType.codes : List UInt8 :=
  [0x53, 0x50]

inductive SendType where
  | send -- Send
  | possibleDuplicate -- Possible Duplicate
  | unlisted (byte : { byte : UInt8 // byte ∉ SendType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SendType

def toByte : SendType → UInt8
  | .send => 0x53
  | .possibleDuplicate => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SendType :=
  if byte = 0x53 then .send
  else .possibleDuplicate

def ofByte (byte : UInt8) : SendType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SendType) : ofByte value.toByte = value := by
  cases value with
  | send => decide
  | possibleDuplicate => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SendType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SendType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SendType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SendType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SendType

/-- Transaction Type: one byte code -/
def TransactionType.codes : List UInt8 :=
  [0x58, 0x59, 0x5A]

inductive TransactionType where
  | newTrade -- New Trade
  | tradeCorrection -- Trade Correction
  | tradeCancel -- Trade Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionType

def toByte : TransactionType → UInt8
  | .newTrade => 0x58
  | .tradeCorrection => 0x59
  | .tradeCancel => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionType :=
  if byte = 0x58 then .newTrade
  else if byte = 0x59 then .tradeCorrection
  else .tradeCancel

def ofByte (byte : UInt8) : TransactionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionType) : ofByte value.toByte = value := by
  cases value with
  | newTrade => decide
  | tradeCorrection => decide
  | tradeCancel => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TransactionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionType

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x50, 0x4F, 0x53, 0x46, 0x42, 0x20]

inductive AuctionType where
  | simpleOrderPixlPrismPim -- Simple Order Pixl Prism Pim
  | opening -- Opening
  | simpleOrderSolicitation -- Simple Order Solicitation
  | simpleFacilitation -- Simple Facilitation
  | block -- Block
  | noAuction -- No Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .simpleOrderPixlPrismPim => 0x50
  | .opening => 0x4F
  | .simpleOrderSolicitation => 0x53
  | .simpleFacilitation => 0x46
  | .block => 0x42
  | .noAuction => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x50 then .simpleOrderPixlPrismPim
  else if byte = 0x4F then .opening
  else if byte = 0x53 then .simpleOrderSolicitation
  else if byte = 0x46 then .simpleFacilitation
  else if byte = 0x42 then .block
  else .noAuction

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | simpleOrderPixlPrismPim => decide
  | opening => decide
  | simpleOrderSolicitation => decide
  | simpleFacilitation => decide
  | block => decide
  | noAuction => decide
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

/-- Execution Type: one byte code -/
def ExecutionType.codes : List UInt8 :=
  [0x41, 0x4D]

inductive ExecutionType where
  | automatic -- Automatic
  | manual -- Manual
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecutionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecutionType

def toByte : ExecutionType → UInt8
  | .automatic => 0x41
  | .manual => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecutionType :=
  if byte = 0x41 then .automatic
  else .manual

def ofByte (byte : UInt8) : ExecutionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecutionType) : ofByte value.toByte = value := by
  cases value with
  | automatic => decide
  | manual => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecutionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecutionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecutionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExecutionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecutionType

/-- Execution Market: one byte code -/
def ExecutionMarket.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x49, 0x4E, 0x51, 0x57, 0x5A, 0x58, 0x54, 0x4D, 0x50, 0x48, 0x45, 0x4A, 0x55, 0x53, 0x56, 0x47, 0x20]

inductive ExecutionMarket where
  | amex -- Amex
  | box -- Box
  | cboe -- Cboe
  | miaxEmerald -- Miax Emerald
  | ise -- Ise
  | nyse -- Nyse
  | nasdaq -- Nasdaq
  | c2 -- C 2
  | bats -- Bats
  | phlx -- Phlx
  | ntxOptions -- Ntx Options
  | miax -- Miax
  | miaxPearl -- Miax Pearl
  | gemx -- Gemx
  | batsEdgx -- Bats Edgx
  | mrx -- Mrx
  | memx -- Memx
  | miaxSapphire -- Miax Sapphire
  | iex -- Iex
  | mx2 -- Mx 2
  | notAwayTrade -- Not Away Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecutionMarket.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecutionMarket

def toByte : ExecutionMarket → UInt8
  | .amex => 0x41
  | .box => 0x42
  | .cboe => 0x43
  | .miaxEmerald => 0x44
  | .ise => 0x49
  | .nyse => 0x4E
  | .nasdaq => 0x51
  | .c2 => 0x57
  | .bats => 0x5A
  | .phlx => 0x58
  | .ntxOptions => 0x54
  | .miax => 0x4D
  | .miaxPearl => 0x50
  | .gemx => 0x48
  | .batsEdgx => 0x45
  | .mrx => 0x4A
  | .memx => 0x55
  | .miaxSapphire => 0x53
  | .iex => 0x56
  | .mx2 => 0x47
  | .notAwayTrade => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecutionMarket :=
  if byte = 0x41 then .amex
  else if byte = 0x42 then .box
  else if byte = 0x43 then .cboe
  else if byte = 0x44 then .miaxEmerald
  else if byte = 0x49 then .ise
  else if byte = 0x4E then .nyse
  else if byte = 0x51 then .nasdaq
  else if byte = 0x57 then .c2
  else if byte = 0x5A then .bats
  else if byte = 0x58 then .phlx
  else if byte = 0x54 then .ntxOptions
  else if byte = 0x4D then .miax
  else if byte = 0x50 then .miaxPearl
  else if byte = 0x48 then .gemx
  else if byte = 0x45 then .batsEdgx
  else if byte = 0x4A then .mrx
  else if byte = 0x55 then .memx
  else if byte = 0x53 then .miaxSapphire
  else if byte = 0x56 then .iex
  else if byte = 0x47 then .mx2
  else .notAwayTrade

def ofByte (byte : UInt8) : ExecutionMarket :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecutionMarket) : ofByte value.toByte = value := by
  cases value with
  | amex => decide
  | box => decide
  | cboe => decide
  | miaxEmerald => decide
  | ise => decide
  | nyse => decide
  | nasdaq => decide
  | c2 => decide
  | bats => decide
  | phlx => decide
  | ntxOptions => decide
  | miax => decide
  | miaxPearl => decide
  | gemx => decide
  | batsEdgx => decide
  | mrx => decide
  | memx => decide
  | miaxSapphire => decide
  | iex => decide
  | mx2 => decide
  | notAwayTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecutionMarket) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecutionMarket × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecutionMarket) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExecutionMarket) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecutionMarket

/-- Trade Side: one byte code -/
def TradeSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive TradeSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeSide

def toByte : TradeSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : TradeSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeSide

/-- Side Changed: one byte code -/
def SideChanged.codes : List UInt8 :=
  [0x59, 0x4E]

inductive SideChanged where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ SideChanged.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SideChanged

def toByte : SideChanged → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SideChanged :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : SideChanged :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SideChanged) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SideChanged) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SideChanged × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SideChanged) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SideChanged) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SideChanged

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x43, 0x50, 0x42, 0x4D, 0x4F, 0x20, 0x4A, 0x46]

inductive Capacity where
  | customer -- Customer
  | professionalCustomer -- Professional Customer
  | brokerDealerCustomer -- Broker Dealer Customer
  | exchangeRegisteredMarketMaker -- Exchange Registered Market Maker
  | otherExchangeRegisteredMarketMaker -- Other Exchange Registered Market Maker
  | notApplicable -- Not Applicable
  | jointBackOffice -- Joint Back Office
  | firm -- Firm
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .customer => 0x43
  | .professionalCustomer => 0x50
  | .brokerDealerCustomer => 0x42
  | .exchangeRegisteredMarketMaker => 0x4D
  | .otherExchangeRegisteredMarketMaker => 0x4F
  | .notApplicable => 0x20
  | .jointBackOffice => 0x4A
  | .firm => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x43 then .customer
  else if byte = 0x50 then .professionalCustomer
  else if byte = 0x42 then .brokerDealerCustomer
  else if byte = 0x4D then .exchangeRegisteredMarketMaker
  else if byte = 0x4F then .otherExchangeRegisteredMarketMaker
  else if byte = 0x20 then .notApplicable
  else if byte = 0x4A then .jointBackOffice
  else .firm

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | professionalCustomer => decide
  | brokerDealerCustomer => decide
  | exchangeRegisteredMarketMaker => decide
  | otherExchangeRegisteredMarketMaker => decide
  | notApplicable => decide
  | jointBackOffice => decide
  | firm => decide
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

/-- Origin Market: one byte code -/
def OriginMarket.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x49, 0x4E, 0x51, 0x57, 0x58, 0x54, 0x4D, 0x48, 0x45, 0x4A, 0x55, 0x53, 0x56, 0x47, 0x20]

inductive OriginMarket where
  | amex -- Amex
  | box -- Box
  | cboe -- Cboe
  | miaxEmerald -- Miax Emerald
  | ise -- Ise
  | nyse -- Nyse
  | nasdaq -- Nasdaq
  | c2 -- C 2
  | phlx -- Phlx
  | ntxOptions -- Ntx Options
  | miax -- Miax
  | gemx -- Gemx
  | batsEdgx -- Bats Edgx
  | mrx -- Mrx
  | memx -- Memx
  | miaxSapphire -- Miax Sapphire
  | iex -- Iex
  | mx2 -- Mx 2
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginMarket.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginMarket

def toByte : OriginMarket → UInt8
  | .amex => 0x41
  | .box => 0x42
  | .cboe => 0x43
  | .miaxEmerald => 0x44
  | .ise => 0x49
  | .nyse => 0x4E
  | .nasdaq => 0x51
  | .c2 => 0x57
  | .phlx => 0x58
  | .ntxOptions => 0x54
  | .miax => 0x4D
  | .gemx => 0x48
  | .batsEdgx => 0x45
  | .mrx => 0x4A
  | .memx => 0x55
  | .miaxSapphire => 0x53
  | .iex => 0x56
  | .mx2 => 0x47
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginMarket :=
  if byte = 0x41 then .amex
  else if byte = 0x42 then .box
  else if byte = 0x43 then .cboe
  else if byte = 0x44 then .miaxEmerald
  else if byte = 0x49 then .ise
  else if byte = 0x4E then .nyse
  else if byte = 0x51 then .nasdaq
  else if byte = 0x57 then .c2
  else if byte = 0x58 then .phlx
  else if byte = 0x54 then .ntxOptions
  else if byte = 0x4D then .miax
  else if byte = 0x48 then .gemx
  else if byte = 0x45 then .batsEdgx
  else if byte = 0x4A then .mrx
  else if byte = 0x55 then .memx
  else if byte = 0x53 then .miaxSapphire
  else if byte = 0x56 then .iex
  else if byte = 0x47 then .mx2
  else .notApplicable

def ofByte (byte : UInt8) : OriginMarket :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginMarket) : ofByte value.toByte = value := by
  cases value with
  | amex => decide
  | box => decide
  | cboe => decide
  | miaxEmerald => decide
  | ise => decide
  | nyse => decide
  | nasdaq => decide
  | c2 => decide
  | phlx => decide
  | ntxOptions => decide
  | miax => decide
  | gemx => decide
  | batsEdgx => decide
  | mrx => decide
  | memx => decide
  | miaxSapphire => decide
  | iex => decide
  | mx2 => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginMarket) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginMarket × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginMarket) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginMarket) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginMarket

/-- Contra Capacity: one byte code -/
def ContraCapacity.codes : List UInt8 :=
  [0x43, 0x45, 0x52, 0x50, 0x42, 0x4D, 0x4F, 0x20, 0x4A, 0x46, 0x66, 0x4B]

inductive ContraCapacity where
  | customer -- Customer
  | proprietaryCustomer -- Proprietary Customer
  | retailCustomer -- Retail Customer
  | professionalCustomer -- Professional Customer
  | brokerDealerCustomer -- Broker Dealer Customer
  | exchangeRegisteredMarketMaker -- Exchange Registered Market Maker
  | otherExchangeRegisteredMarketMaker -- Other Exchange Registered Market Maker
  | notApplicable -- Not Applicable
  | jointBackOffice -- Joint Back Office
  | firm -- Firm
  | proprietaryFirm -- Proprietary Firm
  | brokerDealerFirm -- Broker Dealer Firm
  | unlisted (byte : { byte : UInt8 // byte ∉ ContraCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContraCapacity

def toByte : ContraCapacity → UInt8
  | .customer => 0x43
  | .proprietaryCustomer => 0x45
  | .retailCustomer => 0x52
  | .professionalCustomer => 0x50
  | .brokerDealerCustomer => 0x42
  | .exchangeRegisteredMarketMaker => 0x4D
  | .otherExchangeRegisteredMarketMaker => 0x4F
  | .notApplicable => 0x20
  | .jointBackOffice => 0x4A
  | .firm => 0x46
  | .proprietaryFirm => 0x66
  | .brokerDealerFirm => 0x4B
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContraCapacity :=
  if byte = 0x43 then .customer
  else if byte = 0x45 then .proprietaryCustomer
  else if byte = 0x52 then .retailCustomer
  else if byte = 0x50 then .professionalCustomer
  else if byte = 0x42 then .brokerDealerCustomer
  else if byte = 0x4D then .exchangeRegisteredMarketMaker
  else if byte = 0x4F then .otherExchangeRegisteredMarketMaker
  else if byte = 0x20 then .notApplicable
  else if byte = 0x4A then .jointBackOffice
  else if byte = 0x46 then .firm
  else if byte = 0x66 then .proprietaryFirm
  else .brokerDealerFirm

def ofByte (byte : UInt8) : ContraCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContraCapacity) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | proprietaryCustomer => decide
  | retailCustomer => decide
  | professionalCustomer => decide
  | brokerDealerCustomer => decide
  | exchangeRegisteredMarketMaker => decide
  | otherExchangeRegisteredMarketMaker => decide
  | notApplicable => decide
  | jointBackOffice => decide
  | firm => decide
  | proprietaryFirm => decide
  | brokerDealerFirm => decide
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

/-- Short Sell: one byte code -/
def ShortSell.codes : List UInt8 :=
  [0x59, 0x4E, 0x45, 0x20]

inductive ShortSell where
  | shortSale -- Short Sale
  | notAShortSale -- Not A Short Sale
  | shortSaleExempt -- Short Sale Exempt
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSell.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSell

def toByte : ShortSell → UInt8
  | .shortSale => 0x59
  | .notAShortSale => 0x4E
  | .shortSaleExempt => 0x45
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSell :=
  if byte = 0x59 then .shortSale
  else if byte = 0x4E then .notAShortSale
  else if byte = 0x45 then .shortSaleExempt
  else .notApplicable

def ofByte (byte : UInt8) : ShortSell :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSell) : ofByte value.toByte = value := by
  cases value with
  | shortSale => decide
  | notAShortSale => decide
  | shortSaleExempt => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSell) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSell × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSell) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ShortSell) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSell

/-- Principal Agent: one byte code -/
def PrincipalAgent.codes : List UInt8 :=
  [0x41, 0x50, 0x52, 0x20]

inductive PrincipalAgent where
  | agency -- Agency
  | principal -- Principal
  | risklessPrincipal -- Riskless Principal
  | notAStockLeg -- Not A Stock Leg
  | unlisted (byte : { byte : UInt8 // byte ∉ PrincipalAgent.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrincipalAgent

def toByte : PrincipalAgent → UInt8
  | .agency => 0x41
  | .principal => 0x50
  | .risklessPrincipal => 0x52
  | .notAStockLeg => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrincipalAgent :=
  if byte = 0x41 then .agency
  else if byte = 0x50 then .principal
  else if byte = 0x52 then .risklessPrincipal
  else .notAStockLeg

def ofByte (byte : UInt8) : PrincipalAgent :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrincipalAgent) : ofByte value.toByte = value := by
  cases value with
  | agency => decide
  | principal => decide
  | risklessPrincipal => decide
  | notAStockLeg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrincipalAgent) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrincipalAgent × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrincipalAgent) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrincipalAgent) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrincipalAgent

/-- Origin Type: one byte code -/
def OriginType.codes : List UInt8 :=
  [0x4F, 0x54, 0x51, 0x57, 0x50, 0x58, 0x47, 0x48, 0x49, 0x4A, 0x42, 0x4B, 0x4C, 0x4D, 0x4E, 0x55, 0x56, 0x46, 0x41, 0x44, 0x59, 0x20]

inductive OriginType where
  | fixOrder -- Fix Order
  | ottoOrder -- Otto Order
  | sqfQuote -- Sqf Quote
  | sqfSweep -- Sqf Sweep
  | blockOrder -- Block Order
  | blockResponse -- Block Response
  | pimPrimaryOrder -- Pim Primary Order
  | pimContraOrder -- Pim Contra Order
  | pimResponseOrder -- Pim Response Order
  | pimResponseSqfSweep -- Pim Response Sqf Sweep
  | fbmsFloorTrade -- Fbms Floor Trade
  | qccPrimary -- Qcc Primary
  | qccContra -- Qcc Contra
  | solicitationPrimaryOrder -- Solicitation Primary Order
  | solicitationContraOrder -- Solicitation Contra Order
  | solicitationResponseOrder -- Solicitation Response Order
  | solicitationResponseSqfSweep -- Solicitation Response Sqf Sweep
  | facilitationPrimaryOrder -- Facilitation Primary Order
  | facilitationContraOrder -- Facilitation Contra Order
  | facilitationResponseOrder -- Facilitation Response Order
  | facilitationResponseSqfSweep -- Facilitation Response Sqf Sweep
  | others -- Others
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginType

def toByte : OriginType → UInt8
  | .fixOrder => 0x4F
  | .ottoOrder => 0x54
  | .sqfQuote => 0x51
  | .sqfSweep => 0x57
  | .blockOrder => 0x50
  | .blockResponse => 0x58
  | .pimPrimaryOrder => 0x47
  | .pimContraOrder => 0x48
  | .pimResponseOrder => 0x49
  | .pimResponseSqfSweep => 0x4A
  | .fbmsFloorTrade => 0x42
  | .qccPrimary => 0x4B
  | .qccContra => 0x4C
  | .solicitationPrimaryOrder => 0x4D
  | .solicitationContraOrder => 0x4E
  | .solicitationResponseOrder => 0x55
  | .solicitationResponseSqfSweep => 0x56
  | .facilitationPrimaryOrder => 0x46
  | .facilitationContraOrder => 0x41
  | .facilitationResponseOrder => 0x44
  | .facilitationResponseSqfSweep => 0x59
  | .others => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginType :=
  if byte = 0x4F then .fixOrder
  else if byte = 0x54 then .ottoOrder
  else if byte = 0x51 then .sqfQuote
  else if byte = 0x57 then .sqfSweep
  else if byte = 0x50 then .blockOrder
  else if byte = 0x58 then .blockResponse
  else if byte = 0x47 then .pimPrimaryOrder
  else if byte = 0x48 then .pimContraOrder
  else if byte = 0x49 then .pimResponseOrder
  else if byte = 0x4A then .pimResponseSqfSweep
  else if byte = 0x42 then .fbmsFloorTrade
  else if byte = 0x4B then .qccPrimary
  else if byte = 0x4C then .qccContra
  else if byte = 0x4D then .solicitationPrimaryOrder
  else if byte = 0x4E then .solicitationContraOrder
  else if byte = 0x55 then .solicitationResponseOrder
  else if byte = 0x56 then .solicitationResponseSqfSweep
  else if byte = 0x46 then .facilitationPrimaryOrder
  else if byte = 0x41 then .facilitationContraOrder
  else if byte = 0x44 then .facilitationResponseOrder
  else if byte = 0x59 then .facilitationResponseSqfSweep
  else .others

def ofByte (byte : UInt8) : OriginType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginType) : ofByte value.toByte = value := by
  cases value with
  | fixOrder => decide
  | ottoOrder => decide
  | sqfQuote => decide
  | sqfSweep => decide
  | blockOrder => decide
  | blockResponse => decide
  | pimPrimaryOrder => decide
  | pimContraOrder => decide
  | pimResponseOrder => decide
  | pimResponseSqfSweep => decide
  | fbmsFloorTrade => decide
  | qccPrimary => decide
  | qccContra => decide
  | solicitationPrimaryOrder => decide
  | solicitationContraOrder => decide
  | solicitationResponseOrder => decide
  | solicitationResponseSqfSweep => decide
  | facilitationPrimaryOrder => decide
  | facilitationContraOrder => decide
  | facilitationResponseOrder => decide
  | facilitationResponseSqfSweep => decide
  | others => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginType

/-- Tif: one byte code -/
def Tif.codes : List UInt8 :=
  [0x49, 0x44, 0x47, 0x4F, 0x54, 0x20]

inductive Tif where
  | iocOrFok -- Ioc Or Fok
  | day -- Day
  | gtc -- Gtc
  | opg -- Opg
  | gtd -- Gtd
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ Tif.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tif

def toByte : Tif → UInt8
  | .iocOrFok => 0x49
  | .day => 0x44
  | .gtc => 0x47
  | .opg => 0x4F
  | .gtd => 0x54
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tif :=
  if byte = 0x49 then .iocOrFok
  else if byte = 0x44 then .day
  else if byte = 0x47 then .gtc
  else if byte = 0x4F then .opg
  else if byte = 0x54 then .gtd
  else .notApplicable

def ofByte (byte : UInt8) : Tif :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tif) : ofByte value.toByte = value := by
  cases value with
  | iocOrFok => decide
  | day => decide
  | gtc => decide
  | opg => decide
  | gtd => decide
  | notApplicable => decide
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

/-- Debug Packet -/
structure DebugPacket where
  debugText : Capped 65197
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  message.debugText.val

def decode (bytes : List UInt8) : Option DebugPacket := do
  let debugText_ := bytes
  if fits_debugText : debugText_.length ≤ 65197 then
    pure { debugText := ⟨debugText_, fits_debugText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DebugPacket) : (encode message).length ≤ 65197 := by
  have bound_debugText := message.debugText.length_le
  unfold encode
  omega

theorem decode_encode (message : DebugPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.debugText.length_le]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginAcceptedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRejectedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRejectedPacket

/-- System Event Message: 10 bytes -/
structure SystemEventMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  version : BitVec 8
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 1 message.version
    ++ (EventCode.encode message.eventCode)))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ seconds, nanoseconds, version, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 10 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Options Directory Message: 65 bytes -/
structure OptionsDirectoryMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  version : BitVec 8
  optionId : BitVec 32
  securitySymbol : Alpha 8
  expiration : BitVec 16
  strikePrice : BitVec 32
  optionKind : OptionKind
  underlyingSymbol : Alpha 13
  optionClosingType : OptionClosingType
  tradable : Tradable
  mpv : Mpv
  closingOnly : ClosingOnly
  contractSize : BitVec 32
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace OptionsDirectoryMessage

def encode (message : OptionsDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 1 message.version
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 2 message.expiration
    ++ (encodeUInt 4 message.strikePrice
    ++ (OptionKind.encode message.optionKind
    ++ (Alpha.encode message.underlyingSymbol
    ++ (OptionClosingType.encode message.optionClosingType
    ++ (Tradable.encode message.tradable
    ++ (Mpv.encode message.mpv
    ++ (ClosingOnly.encode message.closingOnly
    ++ (encodeUInt 4 message.contractSize
    ++ (Alpha.encode message.reserved16))))))))))))))

def decode (bytes : List UInt8) : Option (OptionsDirectoryMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 8 bytes
  let (expiration, bytes) ← decodeUInt 2 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionKind, bytes) ← OptionKind.decode bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (optionClosingType, bytes) ← OptionClosingType.decode bytes
  let (tradable_, bytes) ← Tradable.decode bytes
  let (mpv, bytes) ← Mpv.decode bytes
  let (closingOnly, bytes) ← ClosingOnly.decode bytes
  let (contractSize, bytes) ← decodeUInt 4 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ seconds, nanoseconds, version, optionId, securitySymbol, expiration, strikePrice, optionKind, underlyingSymbol, optionClosingType, tradable := tradable_, mpv, closingOnly, contractSize, reserved16 }, bytes)

@[simp] theorem encode_length (message : OptionsDirectoryMessage) : (encode message).length = 65 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionKind.encode_length, OptionClosingType.encode_length, Tradable.encode_length, Mpv.encode_length, ClosingOnly.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionKind.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionClosingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tradable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Mpv.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClosingOnly.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionsDirectoryMessage

/-- Security Trading Action Message: 29 bytes -/
structure SecurityTradingActionMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  version : BitVec 8
  optionId : BitVec 32
  securitySymbol : Alpha 8
  expiration : BitVec 16
  strikePrice : BitVec 32
  optionKind : OptionKind
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace SecurityTradingActionMessage

def encode (message : SecurityTradingActionMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 1 message.version
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 2 message.expiration
    ++ (encodeUInt 4 message.strikePrice
    ++ (OptionKind.encode message.optionKind
    ++ (CurrentTradingState.encode message.currentTradingState))))))))

def decode (bytes : List UInt8) : Option (SecurityTradingActionMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 8 bytes
  let (expiration, bytes) ← decodeUInt 2 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionKind, bytes) ← OptionKind.decode bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ seconds, nanoseconds, version, optionId, securitySymbol, expiration, strikePrice, optionKind, currentTradingState }, bytes)

@[simp] theorem encode_length (message : SecurityTradingActionMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionKind.encode_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : SecurityTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityTradingActionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionKind.decode_encode, some_bind]
  dsimp only
  rw [CurrentTradingState.decode_encode, some_bind]
  rfl

end SecurityTradingActionMessage

/-- Trade Message: 336 bytes -/
structure TradeMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  version : BitVec 8
  sendType : SendType
  optionId : BitVec 32
  underlyingSymbol : Alpha 13
  securitySymbol : Alpha 8
  expiration : BitVec 16
  strikePrice : BitVec 32
  optionKind : OptionKind
  tradeFlags : BitVec 16
  reserved4 : Alpha 4
  transactionType : TransactionType
  liquidity : BitVec 8
  tradeId : BitVec 32
  correctionNumber : BitVec 16
  crossId : BitVec 32
  matchId : BitVec 32
  auctionId : BitVec 32
  auctionType : AuctionType
  refTradeId : BitVec 32
  refCorrectionNumber : BitVec 16
  refMatchId : BitVec 32
  executionType : ExecutionType
  executionMarket : ExecutionMarket
  tradeSide : TradeSide
  tradePrice : BitVec 64
  tradeContracts : BitVec 32
  sideChanged : SideChanged
  strategyId : BitVec 32
  strategyLeg : BitVec 16
  reserved8 : Alpha 8
  occClearingNumber : BitVec 32
  giveUpOccClearingNumber : BitVec 32
  exchangeClearingNumber : BitVec 32
  exchangeHouse : BitVec 32
  exchangeSuffix : Alpha 1
  capacity : Capacity
  multiAccount : Alpha 5
  broker : Alpha 4
  secondBroker : BitVec 32
  originMarket : OriginMarket
  account : Alpha 32
  nscc : BitVec 32
  mpid : Alpha 5
  clearingFlags : BitVec 16
  executingBroker : Alpha 4
  reserved6 : Alpha 6
  contraOccClearingNumber : BitVec 32
  contraGiveUpOccClearingNumber : BitVec 32
  contraExchangeClearingNumber : BitVec 32
  contraExchangeHouse : BitVec 32
  contraCapacity : ContraCapacity
  contraBroker : BitVec 32
  contraSecondBroker : BitVec 32
  contraNscc : BitVec 32
  contraMpid : Alpha 5
  secondReserved8 : Alpha 8
  firm : Alpha 4
  orderDate : BitVec 16
  orderId : Alpha 30
  quoteId : BitVec 64
  sqfSweepId : BitVec 64
  openCloseIndicator : Alpha 1
  customerStrategyLeg : Alpha 10
  shortSell : ShortSell
  principalAgent : PrincipalAgent
  supplementaryId : Alpha 15
  orderIndicators : BitVec 16
  originType : OriginType
  orderSize : BitVec 32
  orderPrice : BitVec 32
  tif : Tif
  thirdReserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 1 message.version
    ++ (SendType.encode message.sendType
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 2 message.expiration
    ++ (encodeUInt 4 message.strikePrice
    ++ (OptionKind.encode message.optionKind
    ++ (encodeUInt 2 message.tradeFlags
    ++ (Alpha.encode message.reserved4
    ++ (TransactionType.encode message.transactionType
    ++ (encodeUInt 1 message.liquidity
    ++ (encodeUInt 4 message.tradeId
    ++ (encodeUInt 2 message.correctionNumber
    ++ (encodeUInt 4 message.crossId
    ++ (encodeUInt 4 message.matchId
    ++ (encodeUInt 4 message.auctionId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.refTradeId
    ++ (encodeUInt 2 message.refCorrectionNumber
    ++ (encodeUInt 4 message.refMatchId
    ++ (ExecutionType.encode message.executionType
    ++ (ExecutionMarket.encode message.executionMarket
    ++ (TradeSide.encode message.tradeSide
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.tradeContracts
    ++ (SideChanged.encode message.sideChanged
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 2 message.strategyLeg
    ++ (Alpha.encode message.reserved8
    ++ (encodeUInt 4 message.occClearingNumber
    ++ (encodeUInt 4 message.giveUpOccClearingNumber
    ++ (encodeUInt 4 message.exchangeClearingNumber
    ++ (encodeUInt 4 message.exchangeHouse
    ++ (Alpha.encode message.exchangeSuffix
    ++ (Capacity.encode message.capacity
    ++ (Alpha.encode message.multiAccount
    ++ (Alpha.encode message.broker
    ++ (encodeUInt 4 message.secondBroker
    ++ (OriginMarket.encode message.originMarket
    ++ (Alpha.encode message.account
    ++ (encodeUInt 4 message.nscc
    ++ (Alpha.encode message.mpid
    ++ (encodeUInt 2 message.clearingFlags
    ++ (Alpha.encode message.executingBroker
    ++ (Alpha.encode message.reserved6
    ++ (encodeUInt 4 message.contraOccClearingNumber
    ++ (encodeUInt 4 message.contraGiveUpOccClearingNumber
    ++ (encodeUInt 4 message.contraExchangeClearingNumber
    ++ (encodeUInt 4 message.contraExchangeHouse
    ++ (ContraCapacity.encode message.contraCapacity
    ++ (encodeUInt 4 message.contraBroker
    ++ (encodeUInt 4 message.contraSecondBroker
    ++ (encodeUInt 4 message.contraNscc
    ++ (Alpha.encode message.contraMpid
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.firm
    ++ (encodeUInt 2 message.orderDate
    ++ (Alpha.encode message.orderId
    ++ (encodeUInt 8 message.quoteId
    ++ (encodeUInt 8 message.sqfSweepId
    ++ (Alpha.encode message.openCloseIndicator
    ++ (Alpha.encode message.customerStrategyLeg
    ++ (ShortSell.encode message.shortSell
    ++ (PrincipalAgent.encode message.principalAgent
    ++ (Alpha.encode message.supplementaryId
    ++ (encodeUInt 2 message.orderIndicators
    ++ (OriginType.encode message.originType
    ++ (encodeUInt 4 message.orderSize
    ++ (encodeUInt 4 message.orderPrice
    ++ (Tif.encode message.tif
    ++ (Alpha.encode message.thirdReserved8)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (sendType, bytes) ← SendType.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (securitySymbol, bytes) ← Alpha.decode 8 bytes
  let (expiration, bytes) ← decodeUInt 2 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionKind, bytes) ← OptionKind.decode bytes
  let (tradeFlags, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (transactionType, bytes) ← TransactionType.decode bytes
  let (liquidity, bytes) ← decodeUInt 1 bytes
  let (tradeId, bytes) ← decodeUInt 4 bytes
  let (correctionNumber, bytes) ← decodeUInt 2 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (refTradeId, bytes) ← decodeUInt 4 bytes
  let (refCorrectionNumber, bytes) ← decodeUInt 2 bytes
  let (refMatchId, bytes) ← decodeUInt 4 bytes
  let (executionType, bytes) ← ExecutionType.decode bytes
  let (executionMarket, bytes) ← ExecutionMarket.decode bytes
  let (tradeSide, bytes) ← TradeSide.decode bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeContracts, bytes) ← decodeUInt 4 bytes
  let (sideChanged, bytes) ← SideChanged.decode bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (strategyLeg, bytes) ← decodeUInt 2 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (occClearingNumber, bytes) ← decodeUInt 4 bytes
  let (giveUpOccClearingNumber, bytes) ← decodeUInt 4 bytes
  let (exchangeClearingNumber, bytes) ← decodeUInt 4 bytes
  let (exchangeHouse, bytes) ← decodeUInt 4 bytes
  let (exchangeSuffix, bytes) ← Alpha.decode 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (multiAccount, bytes) ← Alpha.decode 5 bytes
  let (broker, bytes) ← Alpha.decode 4 bytes
  let (secondBroker, bytes) ← decodeUInt 4 bytes
  let (originMarket, bytes) ← OriginMarket.decode bytes
  let (account, bytes) ← Alpha.decode 32 bytes
  let (nscc, bytes) ← decodeUInt 4 bytes
  let (mpid, bytes) ← Alpha.decode 5 bytes
  let (clearingFlags, bytes) ← decodeUInt 2 bytes
  let (executingBroker, bytes) ← Alpha.decode 4 bytes
  let (reserved6, bytes) ← Alpha.decode 6 bytes
  let (contraOccClearingNumber, bytes) ← decodeUInt 4 bytes
  let (contraGiveUpOccClearingNumber, bytes) ← decodeUInt 4 bytes
  let (contraExchangeClearingNumber, bytes) ← decodeUInt 4 bytes
  let (contraExchangeHouse, bytes) ← decodeUInt 4 bytes
  let (contraCapacity, bytes) ← ContraCapacity.decode bytes
  let (contraBroker, bytes) ← decodeUInt 4 bytes
  let (contraSecondBroker, bytes) ← decodeUInt 4 bytes
  let (contraNscc, bytes) ← decodeUInt 4 bytes
  let (contraMpid, bytes) ← Alpha.decode 5 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (orderDate, bytes) ← decodeUInt 2 bytes
  let (orderId, bytes) ← Alpha.decode 30 bytes
  let (quoteId, bytes) ← decodeUInt 8 bytes
  let (sqfSweepId, bytes) ← decodeUInt 8 bytes
  let (openCloseIndicator, bytes) ← Alpha.decode 1 bytes
  let (customerStrategyLeg, bytes) ← Alpha.decode 10 bytes
  let (shortSell, bytes) ← ShortSell.decode bytes
  let (principalAgent, bytes) ← PrincipalAgent.decode bytes
  let (supplementaryId, bytes) ← Alpha.decode 15 bytes
  let (orderIndicators, bytes) ← decodeUInt 2 bytes
  let (originType, bytes) ← OriginType.decode bytes
  let (orderSize, bytes) ← decodeUInt 4 bytes
  let (orderPrice, bytes) ← decodeUInt 4 bytes
  let (tif, bytes) ← Tif.decode bytes
  let (thirdReserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ seconds, nanoseconds, version, sendType, optionId, underlyingSymbol, securitySymbol, expiration, strikePrice, optionKind, tradeFlags, reserved4, transactionType, liquidity, tradeId, correctionNumber, crossId, matchId, auctionId, auctionType, refTradeId, refCorrectionNumber, refMatchId, executionType, executionMarket, tradeSide, tradePrice, tradeContracts, sideChanged, strategyId, strategyLeg, reserved8, occClearingNumber, giveUpOccClearingNumber, exchangeClearingNumber, exchangeHouse, exchangeSuffix, capacity, multiAccount, broker, secondBroker, originMarket, account, nscc, mpid, clearingFlags, executingBroker, reserved6, contraOccClearingNumber, contraGiveUpOccClearingNumber, contraExchangeClearingNumber, contraExchangeHouse, contraCapacity, contraBroker, contraSecondBroker, contraNscc, contraMpid, secondReserved8, firm, orderDate, orderId, quoteId, sqfSweepId, openCloseIndicator, customerStrategyLeg, shortSell, principalAgent, supplementaryId, orderIndicators, originType, orderSize, orderPrice, tif, thirdReserved8 }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 336 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SendType.encode_length, Alpha.encode_length, OptionKind.encode_length, TransactionType.encode_length, AuctionType.encode_length, ExecutionType.encode_length, ExecutionMarket.encode_length, TradeSide.encode_length, SideChanged.encode_length, Capacity.encode_length, OriginMarket.encode_length, ContraCapacity.encode_length, ShortSell.encode_length, PrincipalAgent.encode_length, OriginType.encode_length, Tif.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SendType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionKind.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionType.decode_encode, some_bind]
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
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecutionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecutionMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SideChanged.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginMarket.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContraCapacity.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSell.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrincipalAgent.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Tif.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Cancel Trade Message: 65 bytes -/
structure CancelTradeMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  version : BitVec 8
  sendType : SendType
  optionId : BitVec 32
  underlyingSymbol : Alpha 13
  securitySymbol : Alpha 8
  expiration : BitVec 16
  strikePrice : BitVec 32
  optionKind : OptionKind
  tradeId : BitVec 32
  correctionNumber : BitVec 16
  crossId : BitVec 32
  tradeSide : TradeSide
  matchId : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace CancelTradeMessage

def encode (message : CancelTradeMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 1 message.version
    ++ (SendType.encode message.sendType
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 2 message.expiration
    ++ (encodeUInt 4 message.strikePrice
    ++ (OptionKind.encode message.optionKind
    ++ (encodeUInt 4 message.tradeId
    ++ (encodeUInt 2 message.correctionNumber
    ++ (encodeUInt 4 message.crossId
    ++ (TradeSide.encode message.tradeSide
    ++ (encodeUInt 4 message.matchId
    ++ (Alpha.encode message.reserved8)))))))))))))))

def decode (bytes : List UInt8) : Option (CancelTradeMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (sendType, bytes) ← SendType.decode bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (securitySymbol, bytes) ← Alpha.decode 8 bytes
  let (expiration, bytes) ← decodeUInt 2 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionKind, bytes) ← OptionKind.decode bytes
  let (tradeId, bytes) ← decodeUInt 4 bytes
  let (correctionNumber, bytes) ← decodeUInt 2 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (tradeSide, bytes) ← TradeSide.decode bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ seconds, nanoseconds, version, sendType, optionId, underlyingSymbol, securitySymbol, expiration, strikePrice, optionKind, tradeId, correctionNumber, crossId, tradeSide, matchId, reserved8 }, bytes)

@[simp] theorem encode_length (message : CancelTradeMessage) : (encode message).length = 65 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SendType.encode_length, Alpha.encode_length, OptionKind.encode_length, TradeSide.encode_length]

theorem encode_length_pos (message : CancelTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SendType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionKind.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelTradeMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | optionsDirectoryMessage (message : OptionsDirectoryMessage) -- "D" 0x44
  | securityTradingActionMessage (message : SecurityTradingActionMessage) -- "H" 0x48
  | tradeMessage (message : TradeMessage) -- "T" 0x54
  | cancelTradeMessage (message : CancelTradeMessage) -- "V" 0x56
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .optionsDirectoryMessage _ => 68
  | .securityTradingActionMessage _ => 72
  | .tradeMessage _ => 84
  | .cancelTradeMessage _ => 86

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .optionsDirectoryMessage message => OptionsDirectoryMessage.encode message
  | .securityTradingActionMessage message => SecurityTradingActionMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .cancelTradeMessage message => CancelTradeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 336 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | optionsDirectoryMessage inner =>
    simp only [encode, OptionsDirectoryMessage.encode_length]
    omega
  | securityTradingActionMessage inner =>
    simp only [encode, SecurityTradingActionMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | cancelTradeMessage inner =>
    simp only [encode, CancelTradeMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 68 then (OptionsDirectoryMessage.decode bytes).map fun (message, rest) => (.optionsDirectoryMessage message, rest)
  else if tag = 72 then (SecurityTradingActionMessage.decode bytes).map fun (message, rest) => (.securityTradingActionMessage message, rest)
  else if tag = 84 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 86 then (CancelTradeMessage.decode bytes).map fun (message, rest) => (.cancelTradeMessage message, rest)
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
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 337 := by
  unfold encode
  cases message.sequencedMessage with
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | optionsDirectoryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OptionsDirectoryMessage.encode_length]
    omega
  | securityTradingActionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SecurityTradingActionMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | cancelTradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, CancelTradeMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedDataPacket

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServerHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServerHeartbeat

/-- End Of Session: 0 bytes -/
structure EndOfSession where
  deriving DecidableEq, Repr

namespace EndOfSession

def encode (_ : EndOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfSession) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EndOfSession

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | serverHeartbeat (message : ServerHeartbeat) -- "H" 0x48
  | endOfSession (message : EndOfSession) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83
  | .serverHeartbeat _ => 72
  | .endOfSession _ => 90

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .endOfSession message => EndOfSession.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 65197 := by
  cases message with
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [encode]
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
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ServerPayload :=
  if tag = 43 then (DebugPacket.decode bytes).map fun message => .debugPacket message
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginAcceptedPacket message) else none
  else if tag = 74 then (LoginRejectedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRejectedPacket message) else none
  else if tag = 83 then (SequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedDataPacket message) else none
  else if tag = 72 then (ServerHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeat message) else none
  else if tag = 90 then (EndOfSession.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfSession message) else none
  else none

theorem decode_encode (message : ServerPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode]
  | loginAcceptedPacket message => simp [decode, encode, tag, LoginAcceptedPacket.decode_encode_nil]
  | loginRejectedPacket message => simp [decode, encode, tag, LoginRejectedPacket.decode_encode_nil]
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode_nil]
  | serverHeartbeat message => simp [decode, encode, tag, ServerHeartbeat.decode_encode_nil]
  | endOfSession message => simp [decode, encode, tag, EndOfSession.decode_encode_nil]

end ServerPayload

/-- Server Soup Bin Tcp Packet -/
structure ServerSoupBinTcpPacket where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupBinTcpPacket

def encodeBody (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option ServerSoupBinTcpPacket := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let serverPayload ← ServerPayload.decode serverPacketType bytes
  pure { serverPayload }

theorem decodeBody_encodeBody (message : ServerSoupBinTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverPayload with
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
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
  | serverHeartbeat inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, EndOfSession.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ServerSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ServerSoupBinTcpPacket × List UInt8) :=
  decodeFramedAll 2 0 decodeBody

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAll_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

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

end Omi.NasdaqGemxoptionsCtiItchV30Server
