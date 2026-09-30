import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Specialized Quote Interface v9.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Note: Server Unsequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Note: Server Soup Bin Tcp Packet's Packet Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqMrxoptionsQuotingSqfV90Server

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

/-- Msar Type: one byte code -/
def MsarType.codes : List UInt8 :=
  [0x41, 0x4D]

inductive MsarType where
  | auctionResponse -- Auction Response
  | marketSweep -- Market Sweep
  | unlisted (byte : { byte : UInt8 // byte ∉ MsarType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MsarType

def toByte : MsarType → UInt8
  | .auctionResponse => 0x41
  | .marketSweep => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MsarType :=
  if byte = 0x41 then .auctionResponse
  else .marketSweep

def ofByte (byte : UInt8) : MsarType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MsarType) : ofByte value.toByte = value := by
  cases value with
  | auctionResponse => decide
  | marketSweep => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MsarType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MsarType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MsarType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MsarType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MsarType

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x2A, 0x54, 0x58, 0x59, 0x5A]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | notDisclosed -- Not Disclosed
  | buyShort -- Buy Short
  | buyShortExempt -- Buy Short Exempt
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .notDisclosed => 0x2A
  | .buyShort => 0x54
  | .buyShortExempt => 0x58
  | .sellShort => 0x59
  | .sellShortExempt => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x2A then .notDisclosed
  else if byte = 0x54 then .buyShort
  else if byte = 0x58 then .buyShortExempt
  else if byte = 0x59 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | notDisclosed => decide
  | buyShort => decide
  | buyShortExempt => decide
  | sellShort => decide
  | sellShortExempt => decide
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

/-- Status Code: one byte code -/
def StatusCode.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x52, 0x53, 0x54, 0x59, 0x5A]

inductive StatusCode where
  | validRequest -- Valid Request
  | invalidBadge -- Invalid Badge
  | invalidInstrumentUnderlying -- Invalid Instrument Underlying
  | notPermitted -- Not Permitted
  | invalidSide -- Invalid Side
  | invalidSize -- Invalid Size
  | invalidPrice -- Invalid Price
  | invalidSpread -- Invalid Spread
  | invalidIndicatorAttribute -- Invalid Indicator Attribute
  | reentryRequired -- Reentry Required
  | openingRotationInProgress -- Opening Rotation In Progress
  | killSwitchReentryRequired -- Kill Switch Reentry Required
  | fullReplenishmentRequired -- Full Replenishment Required
  | activeCounterExceeded -- Active Counter Exceeded
  | tooLateToAct -- Too Late To Act
  | notInFreeTrading -- Not In Free Trading
  | invalidAuctionInformation -- Invalid Auction Information
  | marketClosed -- Market Closed
  | postOnlyReprice -- Post Only Reprice
  | requestPending -- Request Pending
  | invalidFormatBadBlock -- Invalid Format Bad Block
  | systemError -- System Error
  | unlisted (byte : { byte : UInt8 // byte ∉ StatusCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StatusCode

def toByte : StatusCode → UInt8
  | .validRequest => 0x20
  | .invalidBadge => 0x41
  | .invalidInstrumentUnderlying => 0x42
  | .notPermitted => 0x43
  | .invalidSide => 0x44
  | .invalidSize => 0x45
  | .invalidPrice => 0x46
  | .invalidSpread => 0x47
  | .invalidIndicatorAttribute => 0x48
  | .reentryRequired => 0x49
  | .openingRotationInProgress => 0x4A
  | .killSwitchReentryRequired => 0x4B
  | .fullReplenishmentRequired => 0x4C
  | .activeCounterExceeded => 0x4D
  | .tooLateToAct => 0x4E
  | .notInFreeTrading => 0x50
  | .invalidAuctionInformation => 0x51
  | .marketClosed => 0x52
  | .postOnlyReprice => 0x53
  | .requestPending => 0x54
  | .invalidFormatBadBlock => 0x59
  | .systemError => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StatusCode :=
  if byte = 0x20 then .validRequest
  else if byte = 0x41 then .invalidBadge
  else if byte = 0x42 then .invalidInstrumentUnderlying
  else if byte = 0x43 then .notPermitted
  else if byte = 0x44 then .invalidSide
  else if byte = 0x45 then .invalidSize
  else if byte = 0x46 then .invalidPrice
  else if byte = 0x47 then .invalidSpread
  else if byte = 0x48 then .invalidIndicatorAttribute
  else if byte = 0x49 then .reentryRequired
  else if byte = 0x4A then .openingRotationInProgress
  else if byte = 0x4B then .killSwitchReentryRequired
  else if byte = 0x4C then .fullReplenishmentRequired
  else if byte = 0x4D then .activeCounterExceeded
  else if byte = 0x4E then .tooLateToAct
  else if byte = 0x50 then .notInFreeTrading
  else if byte = 0x51 then .invalidAuctionInformation
  else if byte = 0x52 then .marketClosed
  else if byte = 0x53 then .postOnlyReprice
  else if byte = 0x54 then .requestPending
  else if byte = 0x59 then .invalidFormatBadBlock
  else .systemError

def ofByte (byte : UInt8) : StatusCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StatusCode) : ofByte value.toByte = value := by
  cases value with
  | validRequest => decide
  | invalidBadge => decide
  | invalidInstrumentUnderlying => decide
  | notPermitted => decide
  | invalidSide => decide
  | invalidSize => decide
  | invalidPrice => decide
  | invalidSpread => decide
  | invalidIndicatorAttribute => decide
  | reentryRequired => decide
  | openingRotationInProgress => decide
  | killSwitchReentryRequired => decide
  | fullReplenishmentRequired => decide
  | activeCounterExceeded => decide
  | tooLateToAct => decide
  | notInFreeTrading => decide
  | invalidAuctionInformation => decide
  | marketClosed => decide
  | postOnlyReprice => decide
  | requestPending => decide
  | invalidFormatBadBlock => decide
  | systemError => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StatusCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StatusCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StatusCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StatusCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StatusCode

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

/-- Permitted: one byte code -/
def Permitted.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Permitted where
  | permitted -- Permitted
  | notPermitted -- Not Permitted
  | unlisted (byte : { byte : UInt8 // byte ∉ Permitted.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Permitted

def toByte : Permitted → UInt8
  | .permitted => 0x59
  | .notPermitted => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Permitted :=
  if byte = 0x59 then .permitted
  else .notPermitted

def ofByte (byte : UInt8) : Permitted :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Permitted) : ofByte value.toByte = value := by
  cases value with
  | permitted => decide
  | notPermitted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Permitted) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Permitted × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Permitted) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Permitted) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Permitted

/-- Instrument Type: one byte code -/
def InstrumentType.codes : List UInt8 :=
  [0x53, 0x43, 0x4F]

inductive InstrumentType where
  | simpleInstruments -- Simple Instruments
  | complexInstruments -- Complex Instruments
  | simpleInstrument -- Simple Instrument
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .simpleInstruments => 0x53
  | .complexInstruments => 0x43
  | .simpleInstrument => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentType :=
  if byte = 0x53 then .simpleInstruments
  else if byte = 0x43 then .complexInstruments
  else .simpleInstrument

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | simpleInstruments => decide
  | complexInstruments => decide
  | simpleInstrument => decide
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

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x52, 0x50, 0x44, 0x42, 0x51, 0x57, 0x4E, 0x4C, 0x45, 0x43]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfPreTradingQuote -- Start Of Pre Trading Quote
  | startOfPreTradingOpeningProcess -- Start Of Pre Trading Opening Process
  | endOfPreTrading -- End Of Pre Trading
  | startOfQuote -- Start Of Quote
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
  | .startOfPreTradingQuote => 0x52
  | .startOfPreTradingOpeningProcess => 0x50
  | .endOfPreTrading => 0x44
  | .startOfQuote => 0x42
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
  else if byte = 0x52 then .startOfPreTradingQuote
  else if byte = 0x50 then .startOfPreTradingOpeningProcess
  else if byte = 0x44 then .endOfPreTrading
  else if byte = 0x42 then .startOfQuote
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
  | startOfPreTradingQuote => decide
  | startOfPreTradingOpeningProcess => decide
  | endOfPreTrading => decide
  | startOfQuote => decide
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
  | haltInEffect -- Halt In Effect
  | tradingResumed -- Trading Resumed
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .haltInEffect => 0x48
  | .tradingResumed => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x48 then .haltInEffect
  else .tradingResumed

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | haltInEffect => decide
  | tradingResumed => decide
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

/-- Notification Type: one byte code -/
def NotificationType.codes : List UInt8 :=
  [0x45, 0x43]

inductive NotificationType where
  | executed -- Executed
  | cancelled -- Cancelled
  | unlisted (byte : { byte : UInt8 // byte ∉ NotificationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NotificationType

def toByte : NotificationType → UInt8
  | .executed => 0x45
  | .cancelled => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NotificationType :=
  if byte = 0x45 then .executed
  else .cancelled

def ofByte (byte : UInt8) : NotificationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NotificationType) : ofByte value.toByte = value := by
  cases value with
  | executed => decide
  | cancelled => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NotificationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NotificationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NotificationType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NotificationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NotificationType

/-- Block Status Code: one byte code -/
def BlockStatusCode.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x52, 0x53, 0x54, 0x59, 0x5A]

inductive BlockStatusCode where
  | validRequest -- Valid Request
  | invalidBadge -- Invalid Badge
  | invalidInstrumentUnderlying -- Invalid Instrument Underlying
  | notPermitted -- Not Permitted
  | invalidSide -- Invalid Side
  | invalidSize -- Invalid Size
  | invalidPrice -- Invalid Price
  | invalidSpread -- Invalid Spread
  | invalidIndicatorAttribute -- Invalid Indicator Attribute
  | reentryRequired -- Reentry Required
  | openingRotationInProgress -- Opening Rotation In Progress
  | killSwitchReentryRequired -- Kill Switch Reentry Required
  | fullReplenishmentRequired -- Full Replenishment Required
  | activeCounterExceeded -- Active Counter Exceeded
  | tooLateToAct -- Too Late To Act
  | notInFreeTrading -- Not In Free Trading
  | invalidAuctionInformation -- Invalid Auction Information
  | marketClosed -- Market Closed
  | postOnlyReprice -- Post Only Reprice
  | requestPending -- Request Pending
  | invalidFormatBadBlock -- Invalid Format Bad Block
  | systemError -- System Error
  | unlisted (byte : { byte : UInt8 // byte ∉ BlockStatusCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BlockStatusCode

def toByte : BlockStatusCode → UInt8
  | .validRequest => 0x20
  | .invalidBadge => 0x41
  | .invalidInstrumentUnderlying => 0x42
  | .notPermitted => 0x43
  | .invalidSide => 0x44
  | .invalidSize => 0x45
  | .invalidPrice => 0x46
  | .invalidSpread => 0x47
  | .invalidIndicatorAttribute => 0x48
  | .reentryRequired => 0x49
  | .openingRotationInProgress => 0x4A
  | .killSwitchReentryRequired => 0x4B
  | .fullReplenishmentRequired => 0x4C
  | .activeCounterExceeded => 0x4D
  | .tooLateToAct => 0x4E
  | .notInFreeTrading => 0x50
  | .invalidAuctionInformation => 0x51
  | .marketClosed => 0x52
  | .postOnlyReprice => 0x53
  | .requestPending => 0x54
  | .invalidFormatBadBlock => 0x59
  | .systemError => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BlockStatusCode :=
  if byte = 0x20 then .validRequest
  else if byte = 0x41 then .invalidBadge
  else if byte = 0x42 then .invalidInstrumentUnderlying
  else if byte = 0x43 then .notPermitted
  else if byte = 0x44 then .invalidSide
  else if byte = 0x45 then .invalidSize
  else if byte = 0x46 then .invalidPrice
  else if byte = 0x47 then .invalidSpread
  else if byte = 0x48 then .invalidIndicatorAttribute
  else if byte = 0x49 then .reentryRequired
  else if byte = 0x4A then .openingRotationInProgress
  else if byte = 0x4B then .killSwitchReentryRequired
  else if byte = 0x4C then .fullReplenishmentRequired
  else if byte = 0x4D then .activeCounterExceeded
  else if byte = 0x4E then .tooLateToAct
  else if byte = 0x50 then .notInFreeTrading
  else if byte = 0x51 then .invalidAuctionInformation
  else if byte = 0x52 then .marketClosed
  else if byte = 0x53 then .postOnlyReprice
  else if byte = 0x54 then .requestPending
  else if byte = 0x59 then .invalidFormatBadBlock
  else .systemError

def ofByte (byte : UInt8) : BlockStatusCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BlockStatusCode) : ofByte value.toByte = value := by
  cases value with
  | validRequest => decide
  | invalidBadge => decide
  | invalidInstrumentUnderlying => decide
  | notPermitted => decide
  | invalidSide => decide
  | invalidSize => decide
  | invalidPrice => decide
  | invalidSpread => decide
  | invalidIndicatorAttribute => decide
  | reentryRequired => decide
  | openingRotationInProgress => decide
  | killSwitchReentryRequired => decide
  | fullReplenishmentRequired => decide
  | activeCounterExceeded => decide
  | tooLateToAct => decide
  | notInFreeTrading => decide
  | invalidAuctionInformation => decide
  | marketClosed => decide
  | postOnlyReprice => decide
  | requestPending => decide
  | invalidFormatBadBlock => decide
  | systemError => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BlockStatusCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BlockStatusCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BlockStatusCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BlockStatusCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BlockStatusCode

/-- Quote Status Code: one byte code -/
def QuoteStatusCode.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x52, 0x53, 0x54, 0x59, 0x5A]

inductive QuoteStatusCode where
  | validRequest -- Valid Request
  | invalidBadge -- Invalid Badge
  | invalidInstrumentUnderlying -- Invalid Instrument Underlying
  | notPermitted -- Not Permitted
  | invalidSide -- Invalid Side
  | invalidSize -- Invalid Size
  | invalidPrice -- Invalid Price
  | invalidSpread -- Invalid Spread
  | invalidIndicatorAttribute -- Invalid Indicator Attribute
  | reentryRequired -- Reentry Required
  | openingRotationInProgress -- Opening Rotation In Progress
  | killSwitchReentryRequired -- Kill Switch Reentry Required
  | fullReplenishmentRequired -- Full Replenishment Required
  | activeCounterExceeded -- Active Counter Exceeded
  | tooLateToAct -- Too Late To Act
  | notInFreeTrading -- Not In Free Trading
  | invalidAuctionInformation -- Invalid Auction Information
  | marketClosed -- Market Closed
  | postOnlyReprice -- Post Only Reprice
  | requestPending -- Request Pending
  | invalidFormatBadBlock -- Invalid Format Bad Block
  | systemError -- System Error
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteStatusCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteStatusCode

def toByte : QuoteStatusCode → UInt8
  | .validRequest => 0x20
  | .invalidBadge => 0x41
  | .invalidInstrumentUnderlying => 0x42
  | .notPermitted => 0x43
  | .invalidSide => 0x44
  | .invalidSize => 0x45
  | .invalidPrice => 0x46
  | .invalidSpread => 0x47
  | .invalidIndicatorAttribute => 0x48
  | .reentryRequired => 0x49
  | .openingRotationInProgress => 0x4A
  | .killSwitchReentryRequired => 0x4B
  | .fullReplenishmentRequired => 0x4C
  | .activeCounterExceeded => 0x4D
  | .tooLateToAct => 0x4E
  | .notInFreeTrading => 0x50
  | .invalidAuctionInformation => 0x51
  | .marketClosed => 0x52
  | .postOnlyReprice => 0x53
  | .requestPending => 0x54
  | .invalidFormatBadBlock => 0x59
  | .systemError => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteStatusCode :=
  if byte = 0x20 then .validRequest
  else if byte = 0x41 then .invalidBadge
  else if byte = 0x42 then .invalidInstrumentUnderlying
  else if byte = 0x43 then .notPermitted
  else if byte = 0x44 then .invalidSide
  else if byte = 0x45 then .invalidSize
  else if byte = 0x46 then .invalidPrice
  else if byte = 0x47 then .invalidSpread
  else if byte = 0x48 then .invalidIndicatorAttribute
  else if byte = 0x49 then .reentryRequired
  else if byte = 0x4A then .openingRotationInProgress
  else if byte = 0x4B then .killSwitchReentryRequired
  else if byte = 0x4C then .fullReplenishmentRequired
  else if byte = 0x4D then .activeCounterExceeded
  else if byte = 0x4E then .tooLateToAct
  else if byte = 0x50 then .notInFreeTrading
  else if byte = 0x51 then .invalidAuctionInformation
  else if byte = 0x52 then .marketClosed
  else if byte = 0x53 then .postOnlyReprice
  else if byte = 0x54 then .requestPending
  else if byte = 0x59 then .invalidFormatBadBlock
  else .systemError

def ofByte (byte : UInt8) : QuoteStatusCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteStatusCode) : ofByte value.toByte = value := by
  cases value with
  | validRequest => decide
  | invalidBadge => decide
  | invalidInstrumentUnderlying => decide
  | notPermitted => decide
  | invalidSide => decide
  | invalidSize => decide
  | invalidPrice => decide
  | invalidSpread => decide
  | invalidIndicatorAttribute => decide
  | reentryRequired => decide
  | openingRotationInProgress => decide
  | killSwitchReentryRequired => decide
  | fullReplenishmentRequired => decide
  | activeCounterExceeded => decide
  | tooLateToAct => decide
  | notInFreeTrading => decide
  | invalidAuctionInformation => decide
  | marketClosed => decide
  | postOnlyReprice => decide
  | requestPending => decide
  | invalidFormatBadBlock => decide
  | systemError => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteStatusCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteStatusCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteStatusCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : QuoteStatusCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteStatusCode

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
  [0x43, 0x46, 0x4D, 0x4F, 0x50, 0x42, 0x20]

inductive OrderCapacity where
  | customer -- Customer
  | firm -- Firm
  | marketMaker -- Market Maker
  | otherExchangeRegisteredMarketMaker -- Other Exchange Registered Market Maker
  | professionalCustomer -- Professional Customer
  | brokerDealerCustomer -- Broker Dealer Customer
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
  | .brokerDealerCustomer => 0x42
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderCapacity :=
  if byte = 0x43 then .customer
  else if byte = 0x46 then .firm
  else if byte = 0x4D then .marketMaker
  else if byte = 0x4F then .otherExchangeRegisteredMarketMaker
  else if byte = 0x50 then .professionalCustomer
  else if byte = 0x42 then .brokerDealerCustomer
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
  | brokerDealerCustomer => decide
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
  [0x42, 0x43, 0x49, 0x4F, 0x50, 0x48, 0x53]

inductive AuctionType where
  | blockOrderAuction -- Block Order Auction
  | comboExposureAuction -- Combo Exposure Auction
  | orderExposure -- Order Exposure
  | openingAuction -- Opening Auction
  | pimAuction -- Pim Auction
  | facilitationAuction -- Facilitation Auction
  | solicitationAuction -- Solicitation Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .blockOrderAuction => 0x42
  | .comboExposureAuction => 0x43
  | .orderExposure => 0x49
  | .openingAuction => 0x4F
  | .pimAuction => 0x50
  | .facilitationAuction => 0x48
  | .solicitationAuction => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x42 then .blockOrderAuction
  else if byte = 0x43 then .comboExposureAuction
  else if byte = 0x49 then .orderExposure
  else if byte = 0x4F then .openingAuction
  else if byte = 0x50 then .pimAuction
  else if byte = 0x48 then .facilitationAuction
  else .solicitationAuction

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | blockOrderAuction => decide
  | comboExposureAuction => decide
  | orderExposure => decide
  | openingAuction => decide
  | pimAuction => decide
  | facilitationAuction => decide
  | solicitationAuction => decide
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

/-- Purge Reason: one byte code -/
def PurgeReason.codes : List UInt8 :=
  [0x55, 0x53, 0x4B, 0x4D, 0x50, 0x75, 0x73, 0x51]

inductive PurgeReason where
  | userRequestedSimple -- User Requested Simple
  | systemInitiated -- System Initiated
  | autoKillswitch -- Auto Killswitch
  | manualKillswitch -- Manual Killswitch
  | purgeOnDisconnect -- Purge On Disconnect
  | userRequestedComplex -- User Requested Complex
  | systemInitiatedComplex -- System Initiated Complex
  | antiInternalize -- Anti Internalize
  | unlisted (byte : { byte : UInt8 // byte ∉ PurgeReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PurgeReason

def toByte : PurgeReason → UInt8
  | .userRequestedSimple => 0x55
  | .systemInitiated => 0x53
  | .autoKillswitch => 0x4B
  | .manualKillswitch => 0x4D
  | .purgeOnDisconnect => 0x50
  | .userRequestedComplex => 0x75
  | .systemInitiatedComplex => 0x73
  | .antiInternalize => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PurgeReason :=
  if byte = 0x55 then .userRequestedSimple
  else if byte = 0x53 then .systemInitiated
  else if byte = 0x4B then .autoKillswitch
  else if byte = 0x4D then .manualKillswitch
  else if byte = 0x50 then .purgeOnDisconnect
  else if byte = 0x75 then .userRequestedComplex
  else if byte = 0x73 then .systemInitiatedComplex
  else .antiInternalize

def ofByte (byte : UInt8) : PurgeReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PurgeReason) : ofByte value.toByte = value := by
  cases value with
  | userRequestedSimple => decide
  | systemInitiated => decide
  | autoKillswitch => decide
  | manualKillswitch => decide
  | purgeOnDisconnect => decide
  | userRequestedComplex => decide
  | systemInitiatedComplex => decide
  | antiInternalize => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PurgeReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PurgeReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PurgeReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PurgeReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PurgeReason

/-- Reentry Scope: one byte code -/
def ReentryScope.codes : List UInt8 :=
  [0x4E, 0x6E, 0x4B]

inductive ReentryScope where
  | userRequestedSimple -- User Requested Simple
  | userRequestedComplex -- User Requested Complex
  | postKillswitch -- Post Killswitch
  | unlisted (byte : { byte : UInt8 // byte ∉ ReentryScope.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReentryScope

def toByte : ReentryScope → UInt8
  | .userRequestedSimple => 0x4E
  | .userRequestedComplex => 0x6E
  | .postKillswitch => 0x4B
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReentryScope :=
  if byte = 0x4E then .userRequestedSimple
  else if byte = 0x6E then .userRequestedComplex
  else .postKillswitch

def ofByte (byte : UInt8) : ReentryScope :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReentryScope) : ofByte value.toByte = value := by
  cases value with
  | userRequestedSimple => decide
  | userRequestedComplex => decide
  | postKillswitch => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReentryScope) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReentryScope × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReentryScope) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReentryScope) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReentryScope

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

/-- Msar Accept Message: 30 bytes -/
structure MsarAcceptMessage where
  badge : Alpha 4
  messageId : BitVec 64
  instrumentId : BitVec 32
  msarType : MsarType
  auctionId : BitVec 32
  price : BitVec 32
  side : Side
  contracts : BitVec 32
  deriving DecidableEq, Repr

namespace MsarAcceptMessage

def encode (message : MsarAcceptMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 4 message.instrumentId
    ++ (MsarType.encode message.msarType
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 4 message.price
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.contracts)))))))

def decode (bytes : List UInt8) : Option (MsarAcceptMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (msarType, bytes) ← MsarType.decode bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (contracts, bytes) ← decodeUInt 4 bytes
  pure ({ badge, messageId, instrumentId, msarType, auctionId, price, side, contracts }, bytes)

@[simp] theorem encode_length (message : MsarAcceptMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, MsarType.encode_length, Side.encode_length]

theorem encode_length_pos (message : MsarAcceptMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MsarAcceptMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsarType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MsarAcceptMessage

/-- Msar Reject Message: 13 bytes -/
structure MsarRejectMessage where
  badge : Alpha 4
  messageId : BitVec 64
  statusCode : StatusCode
  deriving DecidableEq, Repr

namespace MsarRejectMessage

def encode (message : MsarRejectMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (StatusCode.encode message.statusCode))

def decode (bytes : List UInt8) : Option (MsarRejectMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (statusCode, bytes) ← StatusCode.decode bytes
  pure ({ badge, messageId, statusCode }, bytes)

@[simp] theorem encode_length (message : MsarRejectMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, StatusCode.encode_length]

theorem encode_length_pos (message : MsarRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MsarRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [StatusCode.decode_encode, some_bind]
  rfl

end MsarRejectMessage

/-- Complex Msar Accept Message: 35 bytes -/
structure ComplexMsarAcceptMessage where
  badge : Alpha 4
  messageId : BitVec 64
  instrumentId : BitVec 32
  msarType : MsarType
  auctionId : BitVec 32
  price : BitVec 32
  side : Side
  contracts : BitVec 32
  priceProtection : PriceProtection
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace ComplexMsarAcceptMessage

def encode (message : ComplexMsarAcceptMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 4 message.instrumentId
    ++ (MsarType.encode message.msarType
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 4 message.price
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.contracts
    ++ (PriceProtection.encode message.priceProtection
    ++ (Alpha.encode message.reserved4)))))))))

def decode (bytes : List UInt8) : Option (ComplexMsarAcceptMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (msarType, bytes) ← MsarType.decode bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (contracts, bytes) ← decodeUInt 4 bytes
  let (priceProtection, bytes) ← PriceProtection.decode bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ badge, messageId, instrumentId, msarType, auctionId, price, side, contracts, priceProtection, reserved4 }, bytes)

@[simp] theorem encode_length (message : ComplexMsarAcceptMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, MsarType.encode_length, Side.encode_length, PriceProtection.encode_length]

theorem encode_length_pos (message : ComplexMsarAcceptMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexMsarAcceptMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsarType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PriceProtection.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexMsarAcceptMessage

/-- Complex Msar Reject Message: 13 bytes -/
structure ComplexMsarRejectMessage where
  badge : Alpha 4
  messageId : BitVec 64
  statusCode : StatusCode
  deriving DecidableEq, Repr

namespace ComplexMsarRejectMessage

def encode (message : ComplexMsarRejectMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (StatusCode.encode message.statusCode))

def decode (bytes : List UInt8) : Option (ComplexMsarRejectMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (statusCode, bytes) ← StatusCode.decode bytes
  pure ({ badge, messageId, statusCode }, bytes)

@[simp] theorem encode_length (message : ComplexMsarRejectMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, StatusCode.encode_length]

theorem encode_length_pos (message : ComplexMsarRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexMsarRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [StatusCode.decode_encode, some_bind]
  rfl

end ComplexMsarRejectMessage

/-- Underlying Permission Notification Message: 26 bytes -/
structure UnderlyingPermissionNotificationMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  badge : Alpha 4
  underlying : Alpha 13
  permitted : Permitted
  deriving DecidableEq, Repr

namespace UnderlyingPermissionNotificationMessage

def encode (message : UnderlyingPermissionNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.badge
    ++ (Alpha.encode message.underlying
    ++ (Permitted.encode message.permitted))))

def decode (bytes : List UInt8) : Option (UnderlyingPermissionNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (underlying, bytes) ← Alpha.decode 13 bytes
  let (permitted_, bytes) ← Permitted.decode bytes
  pure ({ seconds, nanoseconds, badge, underlying, permitted := permitted_ }, bytes)

@[simp] theorem encode_length (message : UnderlyingPermissionNotificationMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Permitted.encode_length]

theorem encode_length_pos (message : UnderlyingPermissionNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingPermissionNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Permitted.decode_encode, some_bind]
  rfl

end UnderlyingPermissionNotificationMessage

/-- Mm Parameter Definition Notification Message: 74 bytes -/
structure MmParameterDefinitionNotificationMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  badge : Alpha 4
  instrumentType : InstrumentType
  underlying : Alpha 13
  interval : BitVec 16
  percentage : BitVec 16
  cumQty : BitVec 32
  delta : BitVec 32
  vega : BitVec 32
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace MmParameterDefinitionNotificationMessage

def encode (message : MmParameterDefinitionNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.badge
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.underlying
    ++ (encodeUInt 2 message.interval
    ++ (encodeUInt 2 message.percentage
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 4 message.delta
    ++ (encodeUInt 4 message.vega
    ++ (Alpha.encode message.reserved32))))))))))

def decode (bytes : List UInt8) : Option (MmParameterDefinitionNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (underlying, bytes) ← Alpha.decode 13 bytes
  let (interval, bytes) ← decodeUInt 2 bytes
  let (percentage, bytes) ← decodeUInt 2 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (delta, bytes) ← decodeUInt 4 bytes
  let (vega, bytes) ← decodeUInt 4 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ seconds, nanoseconds, badge, instrumentType, underlying, interval, percentage, cumQty, delta, vega, reserved32 }, bytes)

@[simp] theorem encode_length (message : MmParameterDefinitionNotificationMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length]

theorem encode_length_pos (message : MmParameterDefinitionNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MmParameterDefinitionNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end MmParameterDefinitionNotificationMessage

/-- Active Qp Self Replenishment Parameter Definition Notification Message: 61 bytes -/
structure ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  badge : Alpha 4
  underlying : Alpha 13
  setContractLimit : BitVec 32
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage

def encode (message : ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.badge
    ++ (Alpha.encode message.underlying
    ++ (encodeUInt 4 message.setContractLimit
    ++ (Alpha.encode message.reserved32)))))

def decode (bytes : List UInt8) : Option (ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (underlying, bytes) ← Alpha.decode 13 bytes
  let (setContractLimit, bytes) ← decodeUInt 4 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ seconds, nanoseconds, badge, underlying, setContractLimit, reserved32 }, bytes)

@[simp] theorem encode_length (message : ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage

/-- System Event Message: 11 bytes -/
structure SystemEventMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  eventCode : EventCode
  version : BitVec 8
  subversion : BitVec 8
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 1 message.version
    ++ (encodeUInt 1 message.subversion))))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (subversion, bytes) ← decodeUInt 1 bytes
  pure ({ seconds, nanoseconds, eventCode, version, subversion }, bytes)

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
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Simple Instrument Directory Message: 59 bytes -/
structure SimpleInstrumentDirectoryMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  instrumentId : BitVec 32
  securitySymbol : Alpha 8
  expiration : BitVec 16
  strikePrice : BitVec 32
  optionType : OptionType
  underlyingSymbol : Alpha 13
  closingType : ClosingType
  tradable : Tradable
  mpv : Mpv
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace SimpleInstrumentDirectoryMessage

def encode (message : SimpleInstrumentDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.instrumentId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 2 message.expiration
    ++ (encodeUInt 4 message.strikePrice
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.underlyingSymbol
    ++ (ClosingType.encode message.closingType
    ++ (Tradable.encode message.tradable
    ++ (Mpv.encode message.mpv
    ++ (Alpha.encode message.reserved16)))))))))))

def decode (bytes : List UInt8) : Option (SimpleInstrumentDirectoryMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 8 bytes
  let (expiration, bytes) ← decodeUInt 2 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (closingType, bytes) ← ClosingType.decode bytes
  let (tradable_, bytes) ← Tradable.decode bytes
  let (mpv, bytes) ← Mpv.decode bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ seconds, nanoseconds, instrumentId, securitySymbol, expiration, strikePrice, optionType, underlyingSymbol, closingType, tradable := tradable_, mpv, reserved16 }, bytes)

@[simp] theorem encode_length (message : SimpleInstrumentDirectoryMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, ClosingType.encode_length, Tradable.encode_length, Mpv.encode_length]

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

end SimpleInstrumentDirectoryMessage

/-- Complex Legs: 9 bytes -/
structure ComplexLegs where
  legInstrumentId : BitVec 32
  legSide : LegSide
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace ComplexLegs

def encode (message : ComplexLegs) : List UInt8 :=
  encodeUInt 4 message.legInstrumentId
    ++ (LegSide.encode message.legSide
    ++ (encodeUInt 4 message.legRatio))

def decode (bytes : List UInt8) : Option (ComplexLegs × List UInt8) := do
  let (legInstrumentId, bytes) ← decodeUInt 4 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (legRatio, bytes) ← decodeUInt 4 bytes
  pure ({ legInstrumentId, legSide, legRatio }, bytes)

@[simp] theorem encode_length (message : ComplexLegs) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, LegSide.encode_length]

theorem encode_length_pos (message : ComplexLegs) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexLegs) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ComplexLegs

/-- Complex Instrument Directory Message -/
structure ComplexInstrumentDirectoryMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  instrumentId : BitVec 32
  underlyingSymbol : Alpha 13
  reserved1 : Alpha 1
  complexLegs : Bounded 1 ComplexLegs
  deriving DecidableEq, Repr

namespace ComplexInstrumentDirectoryMessage

def encode (message : ComplexInstrumentDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.instrumentId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.complexLegs.val.length)
    ++ (encodeMany ComplexLegs.encode message.complexLegs.val))))))

def decode (bytes : List UInt8) : Option (ComplexInstrumentDirectoryMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (complexLegs_, bytes) ← decodeMany ComplexLegs.decode numberOfLegs.toNat bytes
  if fits_complexLegs : complexLegs_.length < 256 ^ 1 then
    pure ({ seconds, nanoseconds, instrumentId, underlyingSymbol, reserved1, complexLegs := ⟨complexLegs_, fits_complexLegs⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexInstrumentDirectoryMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexInstrumentDirectoryMessage) : (encode message).length ≤ 2322 := by
  have bound_complexLegs := message.complexLegs.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const ComplexLegs.encode 9 ComplexLegs.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexInstrumentDirectoryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 ComplexLegs.encode ComplexLegs.decode ComplexLegs.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.complexLegs.length_lt]
  rfl

end ComplexInstrumentDirectoryMessage

/-- Simple Instrument Trading Action Message: 13 bytes -/
structure SimpleInstrumentTradingActionMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  instrumentId : BitVec 32
  tradingState : TradingState
  deriving DecidableEq, Repr

namespace SimpleInstrumentTradingActionMessage

def encode (message : SimpleInstrumentTradingActionMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.instrumentId
    ++ (TradingState.encode message.tradingState)))

def decode (bytes : List UInt8) : Option (SimpleInstrumentTradingActionMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  pure ({ seconds, nanoseconds, instrumentId, tradingState }, bytes)

@[simp] theorem encode_length (message : SimpleInstrumentTradingActionMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradingState.encode_length]

theorem encode_length_pos (message : SimpleInstrumentTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleInstrumentTradingActionMessage) (rest : List UInt8) :
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

end SimpleInstrumentTradingActionMessage

/-- Complex Instrument Trading Action Message: 13 bytes -/
structure ComplexInstrumentTradingActionMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  instrumentId : BitVec 32
  tradingState : TradingState
  deriving DecidableEq, Repr

namespace ComplexInstrumentTradingActionMessage

def encode (message : ComplexInstrumentTradingActionMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.instrumentId
    ++ (TradingState.encode message.tradingState)))

def decode (bytes : List UInt8) : Option (ComplexInstrumentTradingActionMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  pure ({ seconds, nanoseconds, instrumentId, tradingState }, bytes)

@[simp] theorem encode_length (message : ComplexInstrumentTradingActionMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradingState.encode_length]

theorem encode_length_pos (message : ComplexInstrumentTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexInstrumentTradingActionMessage) (rest : List UInt8) :
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

end ComplexInstrumentTradingActionMessage

/-- Simple Quote Execution Notification Message: 46 bytes -/
structure SimpleQuoteExecutionNotificationMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  badge : Alpha 4
  instrumentId : BitVec 32
  messageId : BitVec 64
  auctionId : BitVec 32
  price : BitVec 32
  side : Side
  contracts : BitVec 32
  liquidityIndicator : BitVec 8
  crossId : BitVec 32
  matchId : BitVec 32
  deriving DecidableEq, Repr

namespace SimpleQuoteExecutionNotificationMessage

def encode (message : SimpleQuoteExecutionNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.badge
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 4 message.price
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.contracts
    ++ (encodeUInt 1 message.liquidityIndicator
    ++ (encodeUInt 4 message.crossId
    ++ (encodeUInt 4 message.matchId)))))))))))

def decode (bytes : List UInt8) : Option (SimpleQuoteExecutionNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (contracts, bytes) ← decodeUInt 4 bytes
  let (liquidityIndicator, bytes) ← decodeUInt 1 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds, badge, instrumentId, messageId, auctionId, price, side, contracts, liquidityIndicator, crossId, matchId }, bytes)

@[simp] theorem encode_length (message : SimpleQuoteExecutionNotificationMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : SimpleQuoteExecutionNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleQuoteExecutionNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SimpleQuoteExecutionNotificationMessage

/-- Complex Quote Execution Notification Message: 50 bytes -/
structure ComplexQuoteExecutionNotificationMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  badge : Alpha 4
  messageId : BitVec 64
  instrumentId : BitVec 32
  auctionId : BitVec 32
  price6 : BitVec 64
  side : Side
  contracts : BitVec 32
  liquidityIndicator : BitVec 8
  crossId : BitVec 32
  matchId : BitVec 32
  deriving DecidableEq, Repr

namespace ComplexQuoteExecutionNotificationMessage

def encode (message : ComplexQuoteExecutionNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 8 message.price6
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.contracts
    ++ (encodeUInt 1 message.liquidityIndicator
    ++ (encodeUInt 4 message.crossId
    ++ (encodeUInt 4 message.matchId)))))))))))

def decode (bytes : List UInt8) : Option (ComplexQuoteExecutionNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (price6, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (contracts, bytes) ← decodeUInt 4 bytes
  let (liquidityIndicator, bytes) ← decodeUInt 1 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds, badge, messageId, instrumentId, auctionId, price6, side, contracts, liquidityIndicator, crossId, matchId }, bytes)

@[simp] theorem encode_length (message : ComplexQuoteExecutionNotificationMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : ComplexQuoteExecutionNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexQuoteExecutionNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ComplexQuoteExecutionNotificationMessage

/-- Complex Quote Leg Execution Notification Message: 55 bytes -/
structure ComplexQuoteLegExecutionNotificationMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  badge : Alpha 4
  messageId : BitVec 64
  instrumentId : BitVec 32
  legInstrumentId : BitVec 32
  legId : BitVec 8
  auctionId : BitVec 32
  price6 : BitVec 64
  side : Side
  contracts : BitVec 32
  liquidityIndicator : BitVec 8
  crossId : BitVec 32
  matchId : BitVec 32
  deriving DecidableEq, Repr

namespace ComplexQuoteLegExecutionNotificationMessage

def encode (message : ComplexQuoteLegExecutionNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.legInstrumentId
    ++ (encodeUInt 1 message.legId
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 8 message.price6
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.contracts
    ++ (encodeUInt 1 message.liquidityIndicator
    ++ (encodeUInt 4 message.crossId
    ++ (encodeUInt 4 message.matchId)))))))))))))

def decode (bytes : List UInt8) : Option (ComplexQuoteLegExecutionNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (legInstrumentId, bytes) ← decodeUInt 4 bytes
  let (legId, bytes) ← decodeUInt 1 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (price6, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (contracts, bytes) ← decodeUInt 4 bytes
  let (liquidityIndicator, bytes) ← decodeUInt 1 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds, badge, messageId, instrumentId, legInstrumentId, legId, auctionId, price6, side, contracts, liquidityIndicator, crossId, matchId }, bytes)

@[simp] theorem encode_length (message : ComplexQuoteLegExecutionNotificationMessage) : (encode message).length = 55 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : ComplexQuoteLegExecutionNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexQuoteLegExecutionNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ComplexQuoteLegExecutionNotificationMessage

/-- Simple Msar Notification Message: 47 bytes -/
structure SimpleMsarNotificationMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  badge : Alpha 4
  instrumentId : BitVec 32
  notificationType : NotificationType
  messageId : BitVec 64
  auctionId : BitVec 32
  price : BitVec 32
  side : Side
  contracts : BitVec 32
  liquidityIndicator : BitVec 8
  crossId : BitVec 32
  matchId : BitVec 32
  deriving DecidableEq, Repr

namespace SimpleMsarNotificationMessage

def encode (message : SimpleMsarNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.badge
    ++ (encodeUInt 4 message.instrumentId
    ++ (NotificationType.encode message.notificationType
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 4 message.price
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.contracts
    ++ (encodeUInt 1 message.liquidityIndicator
    ++ (encodeUInt 4 message.crossId
    ++ (encodeUInt 4 message.matchId))))))))))))

def decode (bytes : List UInt8) : Option (SimpleMsarNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (notificationType, bytes) ← NotificationType.decode bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (contracts, bytes) ← decodeUInt 4 bytes
  let (liquidityIndicator, bytes) ← decodeUInt 1 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds, badge, instrumentId, notificationType, messageId, auctionId, price, side, contracts, liquidityIndicator, crossId, matchId }, bytes)

@[simp] theorem encode_length (message : SimpleMsarNotificationMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, NotificationType.encode_length, Side.encode_length]

theorem encode_length_pos (message : SimpleMsarNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleMsarNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, NotificationType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SimpleMsarNotificationMessage

/-- Complex Msar Leg Notification Message: 61 bytes -/
structure ComplexMsarLegNotificationMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  badge : Alpha 4
  instrumentId : BitVec 32
  legId : BitVec 8
  legInstrumentId : BitVec 32
  notificationType : NotificationType
  messageId : BitVec 64
  auctionId : BitVec 32
  price : BitVec 32
  side : Side
  legSide : LegSide
  contracts : BitVec 32
  liquidityIndicator : BitVec 8
  crossId : BitVec 32
  matchId : BitVec 32
  price6 : BitVec 64
  deriving DecidableEq, Repr

namespace ComplexMsarLegNotificationMessage

def encode (message : ComplexMsarLegNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.badge
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 1 message.legId
    ++ (encodeUInt 4 message.legInstrumentId
    ++ (NotificationType.encode message.notificationType
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 4 message.price
    ++ (Side.encode message.side
    ++ (LegSide.encode message.legSide
    ++ (encodeUInt 4 message.contracts
    ++ (encodeUInt 1 message.liquidityIndicator
    ++ (encodeUInt 4 message.crossId
    ++ (encodeUInt 4 message.matchId
    ++ (encodeUInt 8 message.price6))))))))))))))))

def decode (bytes : List UInt8) : Option (ComplexMsarLegNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (legId, bytes) ← decodeUInt 1 bytes
  let (legInstrumentId, bytes) ← decodeUInt 4 bytes
  let (notificationType, bytes) ← NotificationType.decode bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (contracts, bytes) ← decodeUInt 4 bytes
  let (liquidityIndicator, bytes) ← decodeUInt 1 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  let (price6, bytes) ← decodeUInt 8 bytes
  pure ({ seconds, nanoseconds, badge, instrumentId, legId, legInstrumentId, notificationType, messageId, auctionId, price, side, legSide, contracts, liquidityIndicator, crossId, matchId, price6 }, bytes)

@[simp] theorem encode_length (message : ComplexMsarLegNotificationMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, NotificationType.encode_length, Side.encode_length, LegSide.encode_length]

theorem encode_length_pos (message : ComplexMsarLegNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexMsarLegNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, NotificationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
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

end ComplexMsarLegNotificationMessage

/-- Complex Msar Notification Message: 55 bytes -/
structure ComplexMsarNotificationMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  badge : Alpha 4
  instrumentId : BitVec 32
  notificationType : NotificationType
  messageId : BitVec 64
  auctionId : BitVec 32
  price : BitVec 32
  side : Side
  contracts : BitVec 32
  liquidityIndicator : BitVec 8
  crossId : BitVec 32
  matchId : BitVec 32
  price6 : BitVec 64
  deriving DecidableEq, Repr

namespace ComplexMsarNotificationMessage

def encode (message : ComplexMsarNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.badge
    ++ (encodeUInt 4 message.instrumentId
    ++ (NotificationType.encode message.notificationType
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 4 message.price
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.contracts
    ++ (encodeUInt 1 message.liquidityIndicator
    ++ (encodeUInt 4 message.crossId
    ++ (encodeUInt 4 message.matchId
    ++ (encodeUInt 8 message.price6)))))))))))))

def decode (bytes : List UInt8) : Option (ComplexMsarNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (notificationType, bytes) ← NotificationType.decode bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (contracts, bytes) ← decodeUInt 4 bytes
  let (liquidityIndicator, bytes) ← decodeUInt 1 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  let (price6, bytes) ← decodeUInt 8 bytes
  pure ({ seconds, nanoseconds, badge, instrumentId, notificationType, messageId, auctionId, price, side, contracts, liquidityIndicator, crossId, matchId, price6 }, bytes)

@[simp] theorem encode_length (message : ComplexMsarNotificationMessage) : (encode message).length = 55 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, NotificationType.encode_length, Side.encode_length]

theorem encode_length_pos (message : ComplexMsarNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexMsarNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, NotificationType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ComplexMsarNotificationMessage

/-- Opening Rotation Quote Spread Multiplier Notification Message: 22 bytes -/
structure OpeningRotationQuoteSpreadMultiplierNotificationMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  underlyingSymbol : Alpha 13
  multiplier : BitVec 8
  deriving DecidableEq, Repr

namespace OpeningRotationQuoteSpreadMultiplierNotificationMessage

def encode (message : OpeningRotationQuoteSpreadMultiplierNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUInt 1 message.multiplier)))

def decode (bytes : List UInt8) : Option (OpeningRotationQuoteSpreadMultiplierNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (multiplier, bytes) ← decodeUInt 1 bytes
  pure ({ seconds, nanoseconds, underlyingSymbol, multiplier }, bytes)

@[simp] theorem encode_length (message : OpeningRotationQuoteSpreadMultiplierNotificationMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OpeningRotationQuoteSpreadMultiplierNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpeningRotationQuoteSpreadMultiplierNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpeningRotationQuoteSpreadMultiplierNotificationMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | msarAcceptMessage (message : MsarAcceptMessage) -- "SA" 0x5341
  | msarRejectMessage (message : MsarRejectMessage) -- "SR" 0x5352
  | complexMsarAcceptMessage (message : ComplexMsarAcceptMessage) -- "SY" 0x5359
  | complexMsarRejectMessage (message : ComplexMsarRejectMessage) -- "SN" 0x534E
  | underlyingPermissionNotificationMessage (message : UnderlyingPermissionNotificationMessage) -- "AP" 0x4150
  | mmParameterDefinitionNotificationMessage (message : MmParameterDefinitionNotificationMessage) -- "AJ" 0x414A
  | activeQpSelfReplenishmentParameterDefinitionNotificationMessage (message : ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage) -- "AK" 0x414B
  | systemEventMessage (message : SystemEventMessage) -- "AS" 0x4153
  | simpleInstrumentDirectoryMessage (message : SimpleInstrumentDirectoryMessage) -- "AD" 0x4144
  | complexInstrumentDirectoryMessage (message : ComplexInstrumentDirectoryMessage) -- "AR" 0x4152
  | simpleInstrumentTradingActionMessage (message : SimpleInstrumentTradingActionMessage) -- "AH" 0x4148
  | complexInstrumentTradingActionMessage (message : ComplexInstrumentTradingActionMessage) -- "AI" 0x4149
  | simpleQuoteExecutionNotificationMessage (message : SimpleQuoteExecutionNotificationMessage) -- "NE" 0x4E45
  | complexQuoteExecutionNotificationMessage (message : ComplexQuoteExecutionNotificationMessage) -- "NV" 0x4E56
  | complexQuoteLegExecutionNotificationMessage (message : ComplexQuoteLegExecutionNotificationMessage) -- "NW" 0x4E57
  | simpleMsarNotificationMessage (message : SimpleMsarNotificationMessage) -- "NS" 0x4E53
  | complexMsarLegNotificationMessage (message : ComplexMsarLegNotificationMessage) -- "NL" 0x4E4C
  | complexMsarNotificationMessage (message : ComplexMsarNotificationMessage) -- "NX" 0x4E58
  | openingRotationQuoteSpreadMultiplierNotificationMessage (message : OpeningRotationQuoteSpreadMultiplierNotificationMessage) -- "AM" 0x414D
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 16
  | .msarAcceptMessage _ => 21313
  | .msarRejectMessage _ => 21330
  | .complexMsarAcceptMessage _ => 21337
  | .complexMsarRejectMessage _ => 21326
  | .underlyingPermissionNotificationMessage _ => 16720
  | .mmParameterDefinitionNotificationMessage _ => 16714
  | .activeQpSelfReplenishmentParameterDefinitionNotificationMessage _ => 16715
  | .systemEventMessage _ => 16723
  | .simpleInstrumentDirectoryMessage _ => 16708
  | .complexInstrumentDirectoryMessage _ => 16722
  | .simpleInstrumentTradingActionMessage _ => 16712
  | .complexInstrumentTradingActionMessage _ => 16713
  | .simpleQuoteExecutionNotificationMessage _ => 20037
  | .complexQuoteExecutionNotificationMessage _ => 20054
  | .complexQuoteLegExecutionNotificationMessage _ => 20055
  | .simpleMsarNotificationMessage _ => 20051
  | .complexMsarLegNotificationMessage _ => 20044
  | .complexMsarNotificationMessage _ => 20056
  | .openingRotationQuoteSpreadMultiplierNotificationMessage _ => 16717

def encode : SequencedMessage → List UInt8
  | .msarAcceptMessage message => MsarAcceptMessage.encode message
  | .msarRejectMessage message => MsarRejectMessage.encode message
  | .complexMsarAcceptMessage message => ComplexMsarAcceptMessage.encode message
  | .complexMsarRejectMessage message => ComplexMsarRejectMessage.encode message
  | .underlyingPermissionNotificationMessage message => UnderlyingPermissionNotificationMessage.encode message
  | .mmParameterDefinitionNotificationMessage message => MmParameterDefinitionNotificationMessage.encode message
  | .activeQpSelfReplenishmentParameterDefinitionNotificationMessage message => ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .simpleInstrumentDirectoryMessage message => SimpleInstrumentDirectoryMessage.encode message
  | .complexInstrumentDirectoryMessage message => ComplexInstrumentDirectoryMessage.encode message
  | .simpleInstrumentTradingActionMessage message => SimpleInstrumentTradingActionMessage.encode message
  | .complexInstrumentTradingActionMessage message => ComplexInstrumentTradingActionMessage.encode message
  | .simpleQuoteExecutionNotificationMessage message => SimpleQuoteExecutionNotificationMessage.encode message
  | .complexQuoteExecutionNotificationMessage message => ComplexQuoteExecutionNotificationMessage.encode message
  | .complexQuoteLegExecutionNotificationMessage message => ComplexQuoteLegExecutionNotificationMessage.encode message
  | .simpleMsarNotificationMessage message => SimpleMsarNotificationMessage.encode message
  | .complexMsarLegNotificationMessage message => ComplexMsarLegNotificationMessage.encode message
  | .complexMsarNotificationMessage message => ComplexMsarNotificationMessage.encode message
  | .openingRotationQuoteSpreadMultiplierNotificationMessage message => OpeningRotationQuoteSpreadMultiplierNotificationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 2322 := by
  cases message with
  | msarAcceptMessage inner =>
    simp only [encode, MsarAcceptMessage.encode_length]
    omega
  | msarRejectMessage inner =>
    simp only [encode, MsarRejectMessage.encode_length]
    omega
  | complexMsarAcceptMessage inner =>
    simp only [encode, ComplexMsarAcceptMessage.encode_length]
    omega
  | complexMsarRejectMessage inner =>
    simp only [encode, ComplexMsarRejectMessage.encode_length]
    omega
  | underlyingPermissionNotificationMessage inner =>
    simp only [encode, UnderlyingPermissionNotificationMessage.encode_length]
    omega
  | mmParameterDefinitionNotificationMessage inner =>
    simp only [encode, MmParameterDefinitionNotificationMessage.encode_length]
    omega
  | activeQpSelfReplenishmentParameterDefinitionNotificationMessage inner =>
    simp only [encode, ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage.encode_length]
    omega
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
  | simpleInstrumentTradingActionMessage inner =>
    simp only [encode, SimpleInstrumentTradingActionMessage.encode_length]
    omega
  | complexInstrumentTradingActionMessage inner =>
    simp only [encode, ComplexInstrumentTradingActionMessage.encode_length]
    omega
  | simpleQuoteExecutionNotificationMessage inner =>
    simp only [encode, SimpleQuoteExecutionNotificationMessage.encode_length]
    omega
  | complexQuoteExecutionNotificationMessage inner =>
    simp only [encode, ComplexQuoteExecutionNotificationMessage.encode_length]
    omega
  | complexQuoteLegExecutionNotificationMessage inner =>
    simp only [encode, ComplexQuoteLegExecutionNotificationMessage.encode_length]
    omega
  | simpleMsarNotificationMessage inner =>
    simp only [encode, SimpleMsarNotificationMessage.encode_length]
    omega
  | complexMsarLegNotificationMessage inner =>
    simp only [encode, ComplexMsarLegNotificationMessage.encode_length]
    omega
  | complexMsarNotificationMessage inner =>
    simp only [encode, ComplexMsarNotificationMessage.encode_length]
    omega
  | openingRotationQuoteSpreadMultiplierNotificationMessage inner =>
    simp only [encode, OpeningRotationQuoteSpreadMultiplierNotificationMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 21313 then (MsarAcceptMessage.decode bytes).map fun (message, rest) => (.msarAcceptMessage message, rest)
  else if tag = 21330 then (MsarRejectMessage.decode bytes).map fun (message, rest) => (.msarRejectMessage message, rest)
  else if tag = 21337 then (ComplexMsarAcceptMessage.decode bytes).map fun (message, rest) => (.complexMsarAcceptMessage message, rest)
  else if tag = 21326 then (ComplexMsarRejectMessage.decode bytes).map fun (message, rest) => (.complexMsarRejectMessage message, rest)
  else if tag = 16720 then (UnderlyingPermissionNotificationMessage.decode bytes).map fun (message, rest) => (.underlyingPermissionNotificationMessage message, rest)
  else if tag = 16714 then (MmParameterDefinitionNotificationMessage.decode bytes).map fun (message, rest) => (.mmParameterDefinitionNotificationMessage message, rest)
  else if tag = 16715 then (ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage.decode bytes).map fun (message, rest) => (.activeQpSelfReplenishmentParameterDefinitionNotificationMessage message, rest)
  else if tag = 16723 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 16708 then (SimpleInstrumentDirectoryMessage.decode bytes).map fun (message, rest) => (.simpleInstrumentDirectoryMessage message, rest)
  else if tag = 16722 then (ComplexInstrumentDirectoryMessage.decode bytes).map fun (message, rest) => (.complexInstrumentDirectoryMessage message, rest)
  else if tag = 16712 then (SimpleInstrumentTradingActionMessage.decode bytes).map fun (message, rest) => (.simpleInstrumentTradingActionMessage message, rest)
  else if tag = 16713 then (ComplexInstrumentTradingActionMessage.decode bytes).map fun (message, rest) => (.complexInstrumentTradingActionMessage message, rest)
  else if tag = 20037 then (SimpleQuoteExecutionNotificationMessage.decode bytes).map fun (message, rest) => (.simpleQuoteExecutionNotificationMessage message, rest)
  else if tag = 20054 then (ComplexQuoteExecutionNotificationMessage.decode bytes).map fun (message, rest) => (.complexQuoteExecutionNotificationMessage message, rest)
  else if tag = 20055 then (ComplexQuoteLegExecutionNotificationMessage.decode bytes).map fun (message, rest) => (.complexQuoteLegExecutionNotificationMessage message, rest)
  else if tag = 20051 then (SimpleMsarNotificationMessage.decode bytes).map fun (message, rest) => (.simpleMsarNotificationMessage message, rest)
  else if tag = 20044 then (ComplexMsarLegNotificationMessage.decode bytes).map fun (message, rest) => (.complexMsarLegNotificationMessage message, rest)
  else if tag = 20056 then (ComplexMsarNotificationMessage.decode bytes).map fun (message, rest) => (.complexMsarNotificationMessage message, rest)
  else if tag = 16717 then (OpeningRotationQuoteSpreadMultiplierNotificationMessage.decode bytes).map fun (message, rest) => (.openingRotationQuoteSpreadMultiplierNotificationMessage message, rest)
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
  encodeUInt 2 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequencedMessageType, bytes) ← decodeUInt 2 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 2324 := by
  unfold encode
  cases message.sequencedMessage with
  | msarAcceptMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, MsarAcceptMessage.encode_length]
    omega
  | msarRejectMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, MsarRejectMessage.encode_length]
    omega
  | complexMsarAcceptMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ComplexMsarAcceptMessage.encode_length]
    omega
  | complexMsarRejectMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ComplexMsarRejectMessage.encode_length]
    omega
  | underlyingPermissionNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, UnderlyingPermissionNotificationMessage.encode_length]
    omega
  | mmParameterDefinitionNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, MmParameterDefinitionNotificationMessage.encode_length]
    omega
  | activeQpSelfReplenishmentParameterDefinitionNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage.encode_length]
    omega
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
  | simpleInstrumentTradingActionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SimpleInstrumentTradingActionMessage.encode_length]
    omega
  | complexInstrumentTradingActionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ComplexInstrumentTradingActionMessage.encode_length]
    omega
  | simpleQuoteExecutionNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SimpleQuoteExecutionNotificationMessage.encode_length]
    omega
  | complexQuoteExecutionNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ComplexQuoteExecutionNotificationMessage.encode_length]
    omega
  | complexQuoteLegExecutionNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ComplexQuoteLegExecutionNotificationMessage.encode_length]
    omega
  | simpleMsarNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SimpleMsarNotificationMessage.encode_length]
    omega
  | complexMsarLegNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ComplexMsarLegNotificationMessage.encode_length]
    omega
  | complexMsarNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ComplexMsarNotificationMessage.encode_length]
    omega
  | openingRotationQuoteSpreadMultiplierNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OpeningRotationQuoteSpreadMultiplierNotificationMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

end SequencedDataPacket

/-- Notification Subscription Reply Message: 13 bytes -/
structure NotificationSubscriptionReplyMessage where
  badge : Alpha 4
  messageId : BitVec 64
  statusCode : StatusCode
  deriving DecidableEq, Repr

namespace NotificationSubscriptionReplyMessage

def encode (message : NotificationSubscriptionReplyMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (StatusCode.encode message.statusCode))

def decode (bytes : List UInt8) : Option (NotificationSubscriptionReplyMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (statusCode, bytes) ← StatusCode.decode bytes
  pure ({ badge, messageId, statusCode }, bytes)

@[simp] theorem encode_length (message : NotificationSubscriptionReplyMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, StatusCode.encode_length]

theorem encode_length_pos (message : NotificationSubscriptionReplyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NotificationSubscriptionReplyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [StatusCode.decode_encode, some_bind]
  rfl

end NotificationSubscriptionReplyMessage

/-- Add Complex Instrument Reply Message: 13 bytes -/
structure AddComplexInstrumentReplyMessage where
  badge : Alpha 4
  messageId : BitVec 64
  statusCode : StatusCode
  deriving DecidableEq, Repr

namespace AddComplexInstrumentReplyMessage

def encode (message : AddComplexInstrumentReplyMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (StatusCode.encode message.statusCode))

def decode (bytes : List UInt8) : Option (AddComplexInstrumentReplyMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (statusCode, bytes) ← StatusCode.decode bytes
  pure ({ badge, messageId, statusCode }, bytes)

@[simp] theorem encode_length (message : AddComplexInstrumentReplyMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, StatusCode.encode_length]

theorem encode_length_pos (message : AddComplexInstrumentReplyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddComplexInstrumentReplyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [StatusCode.decode_encode, some_bind]
  rfl

end AddComplexInstrumentReplyMessage

/-- Mm Parameter Definition Reply Message: 13 bytes -/
structure MmParameterDefinitionReplyMessage where
  badge : Alpha 4
  messageId : BitVec 64
  statusCode : StatusCode
  deriving DecidableEq, Repr

namespace MmParameterDefinitionReplyMessage

def encode (message : MmParameterDefinitionReplyMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (StatusCode.encode message.statusCode))

def decode (bytes : List UInt8) : Option (MmParameterDefinitionReplyMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (statusCode, bytes) ← StatusCode.decode bytes
  pure ({ badge, messageId, statusCode }, bytes)

@[simp] theorem encode_length (message : MmParameterDefinitionReplyMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, StatusCode.encode_length]

theorem encode_length_pos (message : MmParameterDefinitionReplyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MmParameterDefinitionReplyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [StatusCode.decode_encode, some_bind]
  rfl

end MmParameterDefinitionReplyMessage

/-- Active Qp Self Replenishment Set Limit Reply Message: 30 bytes -/
structure ActiveQpSelfReplenishmentSetLimitReplyMessage where
  badge : Alpha 4
  messageId : BitVec 64
  underlyingSymbol : Alpha 13
  setValue : BitVec 32
  statusCode : StatusCode
  deriving DecidableEq, Repr

namespace ActiveQpSelfReplenishmentSetLimitReplyMessage

def encode (message : ActiveQpSelfReplenishmentSetLimitReplyMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUInt 4 message.setValue
    ++ (StatusCode.encode message.statusCode))))

def decode (bytes : List UInt8) : Option (ActiveQpSelfReplenishmentSetLimitReplyMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (setValue, bytes) ← decodeUInt 4 bytes
  let (statusCode, bytes) ← StatusCode.decode bytes
  pure ({ badge, messageId, underlyingSymbol, setValue, statusCode }, bytes)

@[simp] theorem encode_length (message : ActiveQpSelfReplenishmentSetLimitReplyMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, StatusCode.encode_length]

theorem encode_length_pos (message : ActiveQpSelfReplenishmentSetLimitReplyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveQpSelfReplenishmentSetLimitReplyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [StatusCode.decode_encode, some_bind]
  rfl

end ActiveQpSelfReplenishmentSetLimitReplyMessage

/-- Quote Responses: 9 bytes -/
structure QuoteResponses where
  quoteStatusCode : QuoteStatusCode
  sequence : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteResponses

def encode (message : QuoteResponses) : List UInt8 :=
  QuoteStatusCode.encode message.quoteStatusCode
    ++ (encodeUInt 8 message.sequence)

def decode (bytes : List UInt8) : Option (QuoteResponses × List UInt8) := do
  let (quoteStatusCode, bytes) ← QuoteStatusCode.decode bytes
  let (sequence, bytes) ← decodeUInt 8 bytes
  pure ({ quoteStatusCode, sequence }, bytes)

@[simp] theorem encode_length (message : QuoteResponses) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, QuoteStatusCode.encode_length, encodeUInt_length]

theorem encode_length_pos (message : QuoteResponses) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteResponses) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, QuoteStatusCode.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuoteResponses

/-- Quote Block Reply Message -/
structure QuoteBlockReplyMessage where
  badge : Alpha 4
  messageId : BitVec 64
  sentTimestamp : BitVec 64
  blockStatusCode : BlockStatusCode
  quoteCount : BitVec 16
  quoteResponses : Bounded 2 QuoteResponses
  deriving DecidableEq, Repr

namespace QuoteBlockReplyMessage

def encode (message : QuoteBlockReplyMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 8 message.sentTimestamp
    ++ (BlockStatusCode.encode message.blockStatusCode
    ++ (encodeUInt 2 message.quoteCount
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.quoteResponses.val.length)
    ++ (encodeMany QuoteResponses.encode message.quoteResponses.val))))))

def decode (bytes : List UInt8) : Option (QuoteBlockReplyMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (sentTimestamp, bytes) ← decodeUInt 8 bytes
  let (blockStatusCode, bytes) ← BlockStatusCode.decode bytes
  let (quoteCount, bytes) ← decodeUInt 2 bytes
  let (validQuoteCount, bytes) ← decodeUInt 2 bytes
  let (quoteResponses_, bytes) ← decodeMany QuoteResponses.decode validQuoteCount.toNat bytes
  if fits_quoteResponses : quoteResponses_.length < 256 ^ 2 then
    pure ({ badge, messageId, sentTimestamp, blockStatusCode, quoteCount, quoteResponses := ⟨quoteResponses_, fits_quoteResponses⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteBlockReplyMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteBlockReplyMessage) : (encode message).length ≤ 589840 := by
  have bound_quoteResponses := message.quoteResponses.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, BlockStatusCode.encode_length, encodeMany_length_const QuoteResponses.encode 9 QuoteResponses.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteBlockReplyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BlockStatusCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 QuoteResponses.encode QuoteResponses.decode QuoteResponses.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteResponses.length_lt]
  rfl

end QuoteBlockReplyMessage

/-- Detailed Quote Responses: 25 bytes -/
structure DetailedQuoteResponses where
  quoteStatusCode : QuoteStatusCode
  sequence : BitVec 64
  bidSequence : BitVec 64
  askSequence : BitVec 64
  deriving DecidableEq, Repr

namespace DetailedQuoteResponses

def encode (message : DetailedQuoteResponses) : List UInt8 :=
  QuoteStatusCode.encode message.quoteStatusCode
    ++ (encodeUInt 8 message.sequence
    ++ (encodeUInt 8 message.bidSequence
    ++ (encodeUInt 8 message.askSequence)))

def decode (bytes : List UInt8) : Option (DetailedQuoteResponses × List UInt8) := do
  let (quoteStatusCode, bytes) ← QuoteStatusCode.decode bytes
  let (sequence, bytes) ← decodeUInt 8 bytes
  let (bidSequence, bytes) ← decodeUInt 8 bytes
  let (askSequence, bytes) ← decodeUInt 8 bytes
  pure ({ quoteStatusCode, sequence, bidSequence, askSequence }, bytes)

@[simp] theorem encode_length (message : DetailedQuoteResponses) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, QuoteStatusCode.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DetailedQuoteResponses) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DetailedQuoteResponses) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, QuoteStatusCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DetailedQuoteResponses

/-- Detailed Quote Block Reply Message -/
structure DetailedQuoteBlockReplyMessage where
  badge : Alpha 4
  messageId : BitVec 64
  sentTimestamp : BitVec 64
  blockStatusCode : BlockStatusCode
  quoteCount : BitVec 16
  detailedQuoteResponses : Bounded 2 DetailedQuoteResponses
  deriving DecidableEq, Repr

namespace DetailedQuoteBlockReplyMessage

def encode (message : DetailedQuoteBlockReplyMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 8 message.sentTimestamp
    ++ (BlockStatusCode.encode message.blockStatusCode
    ++ (encodeUInt 2 message.quoteCount
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.detailedQuoteResponses.val.length)
    ++ (encodeMany DetailedQuoteResponses.encode message.detailedQuoteResponses.val))))))

def decode (bytes : List UInt8) : Option (DetailedQuoteBlockReplyMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (sentTimestamp, bytes) ← decodeUInt 8 bytes
  let (blockStatusCode, bytes) ← BlockStatusCode.decode bytes
  let (quoteCount, bytes) ← decodeUInt 2 bytes
  let (validQuoteCount, bytes) ← decodeUInt 2 bytes
  let (detailedQuoteResponses_, bytes) ← decodeMany DetailedQuoteResponses.decode validQuoteCount.toNat bytes
  if fits_detailedQuoteResponses : detailedQuoteResponses_.length < 256 ^ 2 then
    pure ({ badge, messageId, sentTimestamp, blockStatusCode, quoteCount, detailedQuoteResponses := ⟨detailedQuoteResponses_, fits_detailedQuoteResponses⟩ }, bytes)
  else none

theorem encode_length_pos (message : DetailedQuoteBlockReplyMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DetailedQuoteBlockReplyMessage) : (encode message).length ≤ 1638400 := by
  have bound_detailedQuoteResponses := message.detailedQuoteResponses.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, BlockStatusCode.encode_length, encodeMany_length_const DetailedQuoteResponses.encode 25 DetailedQuoteResponses.encode_length]
  omega

@[simp] theorem decode_encode (message : DetailedQuoteBlockReplyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BlockStatusCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 DetailedQuoteResponses.encode DetailedQuoteResponses.decode DetailedQuoteResponses.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.detailedQuoteResponses.length_lt]
  rfl

end DetailedQuoteBlockReplyMessage

/-- Underlying Purge Reply Message: 29 bytes -/
structure UnderlyingPurgeReplyMessage where
  badge : Alpha 4
  messageId : BitVec 64
  sentTimestamp : BitVec 64
  statusCode : StatusCode
  sequence : BitVec 64
  deriving DecidableEq, Repr

namespace UnderlyingPurgeReplyMessage

def encode (message : UnderlyingPurgeReplyMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 8 message.sentTimestamp
    ++ (StatusCode.encode message.statusCode
    ++ (encodeUInt 8 message.sequence))))

def decode (bytes : List UInt8) : Option (UnderlyingPurgeReplyMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (sentTimestamp, bytes) ← decodeUInt 8 bytes
  let (statusCode, bytes) ← StatusCode.decode bytes
  let (sequence, bytes) ← decodeUInt 8 bytes
  pure ({ badge, messageId, sentTimestamp, statusCode, sequence }, bytes)

@[simp] theorem encode_length (message : UnderlyingPurgeReplyMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, StatusCode.encode_length]

theorem encode_length_pos (message : UnderlyingPurgeReplyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingPurgeReplyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StatusCode.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end UnderlyingPurgeReplyMessage

/-- Market Reentry Reply Message: 21 bytes -/
structure MarketReentryReplyMessage where
  badge : Alpha 4
  messageId : BitVec 64
  statusCode : StatusCode
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace MarketReentryReplyMessage

def encode (message : MarketReentryReplyMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (StatusCode.encode message.statusCode
    ++ (Alpha.encode message.reserved8)))

def decode (bytes : List UInt8) : Option (MarketReentryReplyMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (statusCode, bytes) ← StatusCode.decode bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ badge, messageId, statusCode, reserved8 }, bytes)

@[simp] theorem encode_length (message : MarketReentryReplyMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, StatusCode.encode_length]

theorem encode_length_pos (message : MarketReentryReplyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketReentryReplyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StatusCode.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketReentryReplyMessage

/-- Active Qp Self Replenishment Request Reentry Reply Message: 38 bytes -/
structure ActiveQpSelfReplenishmentRequestReentryReplyMessage where
  badge : Alpha 4
  messageId : BitVec 64
  underlyingSymbol : Alpha 13
  statusCode : StatusCode
  requestedReplenishmentValue : BitVec 32
  activeCounterValue : BitVec 32
  setContractLimit : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveQpSelfReplenishmentRequestReentryReplyMessage

def encode (message : ActiveQpSelfReplenishmentRequestReentryReplyMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (StatusCode.encode message.statusCode
    ++ (encodeUInt 4 message.requestedReplenishmentValue
    ++ (encodeUInt 4 message.activeCounterValue
    ++ (encodeUInt 4 message.setContractLimit))))))

def decode (bytes : List UInt8) : Option (ActiveQpSelfReplenishmentRequestReentryReplyMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (statusCode, bytes) ← StatusCode.decode bytes
  let (requestedReplenishmentValue, bytes) ← decodeUInt 4 bytes
  let (activeCounterValue, bytes) ← decodeUInt 4 bytes
  let (setContractLimit, bytes) ← decodeUInt 4 bytes
  pure ({ badge, messageId, underlyingSymbol, statusCode, requestedReplenishmentValue, activeCounterValue, setContractLimit }, bytes)

@[simp] theorem encode_length (message : ActiveQpSelfReplenishmentRequestReentryReplyMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, StatusCode.encode_length]

theorem encode_length_pos (message : ActiveQpSelfReplenishmentRequestReentryReplyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveQpSelfReplenishmentRequestReentryReplyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StatusCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveQpSelfReplenishmentRequestReentryReplyMessage

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
  seconds : BitVec 32
  nanoseconds : BitVec 32
  instrumentType : InstrumentType
  instrumentId : BitVec 32
  auctionId : BitVec 32
  orderType : OrderType
  side : Side
  price : BitVec 32
  matchedVolume : BitVec 32
  volume : BitVec 32
  execFlag : ExecFlag
  orderCapacity : OrderCapacity
  firmId : Alpha 4
  occAccount : BitVec 32
  cmta : BitVec 32
  auctionEvent : AuctionEvent
  auctionType : AuctionType
  auctionDuration : BitVec 32
  bestResponsePrice : BitVec 32
  bestResponseSize : BitVec 32
  reserved9 : Alpha 9
  flexDacLegs : Bounded 1 FlexDacLegs
  deriving DecidableEq, Repr

namespace AuctionNotificationMessage

def encode (message : AuctionNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.auctionId
    ++ (OrderType.encode message.orderType
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.matchedVolume
    ++ (encodeUInt 4 message.volume
    ++ (ExecFlag.encode message.execFlag
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (Alpha.encode message.firmId
    ++ (encodeUInt 4 message.occAccount
    ++ (encodeUInt 4 message.cmta
    ++ (AuctionEvent.encode message.auctionEvent
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.auctionDuration
    ++ (encodeUInt 4 message.bestResponsePrice
    ++ (encodeUInt 4 message.bestResponseSize
    ++ (Alpha.encode message.reserved9
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.flexDacLegs.val.length)
    ++ (encodeMany FlexDacLegs.encode message.flexDacLegs.val))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (AuctionNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (matchedVolume, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (execFlag, bytes) ← ExecFlag.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (occAccount, bytes) ← decodeUInt 4 bytes
  let (cmta, bytes) ← decodeUInt 4 bytes
  let (auctionEvent, bytes) ← AuctionEvent.decode bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (auctionDuration, bytes) ← decodeUInt 4 bytes
  let (bestResponsePrice, bytes) ← decodeUInt 4 bytes
  let (bestResponseSize, bytes) ← decodeUInt 4 bytes
  let (reserved9, bytes) ← Alpha.decode 9 bytes
  let (numberOfFlexDacLegs, bytes) ← decodeUInt 1 bytes
  let (flexDacLegs_, bytes) ← decodeMany FlexDacLegs.decode numberOfFlexDacLegs.toNat bytes
  if fits_flexDacLegs : flexDacLegs_.length < 256 ^ 1 then
    pure ({ seconds, nanoseconds, instrumentType, instrumentId, auctionId, orderType, side, price, matchedVolume, volume, execFlag, orderCapacity, firmId, occAccount, cmta, auctionEvent, auctionType, auctionDuration, bestResponsePrice, bestResponseSize, reserved9, flexDacLegs := ⟨flexDacLegs_, fits_flexDacLegs⟩ }, bytes)
  else none

theorem encode_length_pos (message : AuctionNotificationMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AuctionNotificationMessage) : (encode message).length ≤ 2109 := by
  have bound_flexDacLegs := message.flexDacLegs.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, InstrumentType.encode_length, OrderType.encode_length, Side.encode_length, ExecFlag.encode_length, OrderCapacity.encode_length, Alpha.encode_length, AuctionEvent.encode_length, AuctionType.encode_length, encodeMany_length_const FlexDacLegs.encode 8 FlexDacLegs.encode_length]
  omega

@[simp] theorem decode_encode (message : AuctionNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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

/-- Instrument Purge Notification Message: 49 bytes -/
structure InstrumentPurgeNotificationMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  badge : Alpha 4
  messageId : BitVec 64
  instrumentId : BitVec 32
  purgeReason : PurgeReason
  sequence : BitVec 64
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace InstrumentPurgeNotificationMessage

def encode (message : InstrumentPurgeNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 4 message.instrumentId
    ++ (PurgeReason.encode message.purgeReason
    ++ (encodeUInt 8 message.sequence
    ++ (Alpha.encode message.reserved16)))))))

def decode (bytes : List UInt8) : Option (InstrumentPurgeNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (purgeReason, bytes) ← PurgeReason.decode bytes
  let (sequence, bytes) ← decodeUInt 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ seconds, nanoseconds, badge, messageId, instrumentId, purgeReason, sequence, reserved16 }, bytes)

@[simp] theorem encode_length (message : InstrumentPurgeNotificationMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, PurgeReason.encode_length]

theorem encode_length_pos (message : InstrumentPurgeNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentPurgeNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, PurgeReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentPurgeNotificationMessage

/-- Underlying Purge Notification Message: 42 bytes -/
structure UnderlyingPurgeNotificationMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  badge : Alpha 4
  underlying : Alpha 13
  purgeReason : PurgeReason
  messageId : BitVec 64
  sequence : BitVec 64
  deriving DecidableEq, Repr

namespace UnderlyingPurgeNotificationMessage

def encode (message : UnderlyingPurgeNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.badge
    ++ (Alpha.encode message.underlying
    ++ (PurgeReason.encode message.purgeReason
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 8 message.sequence))))))

def decode (bytes : List UInt8) : Option (UnderlyingPurgeNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (underlying, bytes) ← Alpha.decode 13 bytes
  let (purgeReason, bytes) ← PurgeReason.decode bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (sequence, bytes) ← decodeUInt 8 bytes
  pure ({ seconds, nanoseconds, badge, underlying, purgeReason, messageId, sequence }, bytes)

@[simp] theorem encode_length (message : UnderlyingPurgeNotificationMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, PurgeReason.encode_length]

theorem encode_length_pos (message : UnderlyingPurgeNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingPurgeNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PurgeReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end UnderlyingPurgeNotificationMessage

/-- Market Reentry Notification Message: 42 bytes -/
structure MarketReentryNotificationMessage where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  badge : Alpha 4
  underlyingSymbol : Alpha 13
  reentryScope : ReentryScope
  messageId : BitVec 64
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace MarketReentryNotificationMessage

def encode (message : MarketReentryNotificationMessage) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.badge
    ++ (Alpha.encode message.underlyingSymbol
    ++ (ReentryScope.encode message.reentryScope
    ++ (encodeUInt 8 message.messageId
    ++ (Alpha.encode message.reserved8))))))

def decode (bytes : List UInt8) : Option (MarketReentryNotificationMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (reentryScope, bytes) ← ReentryScope.decode bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ seconds, nanoseconds, badge, underlyingSymbol, reentryScope, messageId, reserved8 }, bytes)

@[simp] theorem encode_length (message : MarketReentryNotificationMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ReentryScope.encode_length]

theorem encode_length_pos (message : MarketReentryNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketReentryNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ReentryScope.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketReentryNotificationMessage

/-- Any Server Unsequenced Message, selected by Server Unsequenced Message Type -/
inductive ServerUnsequencedMessage where
  | notificationSubscriptionReplyMessage (message : NotificationSubscriptionReplyMessage) -- "Ab" 0x4162
  | addComplexInstrumentReplyMessage (message : AddComplexInstrumentReplyMessage) -- "Ac" 0x4163
  | mmParameterDefinitionReplyMessage (message : MmParameterDefinitionReplyMessage) -- "Ae" 0x4165
  | activeQpSelfReplenishmentSetLimitReplyMessage (message : ActiveQpSelfReplenishmentSetLimitReplyMessage) -- "Ag" 0x4167
  | quoteBlockReplyMessage (message : QuoteBlockReplyMessage) -- "QS" 0x5153
  | detailedQuoteBlockReplyMessage (message : DetailedQuoteBlockReplyMessage) -- "Qs" 0x5173
  | underlyingPurgeReplyMessage (message : UnderlyingPurgeReplyMessage) -- "Pr" 0x5072
  | marketReentryReplyMessage (message : MarketReentryReplyMessage) -- "RR" 0x5252
  | activeQpSelfReplenishmentRequestReentryReplyMessage (message : ActiveQpSelfReplenishmentRequestReentryReplyMessage) -- "Rg" 0x5267
  | auctionNotificationMessage (message : AuctionNotificationMessage) -- "NA" 0x4E41
  | instrumentPurgeNotificationMessage (message : InstrumentPurgeNotificationMessage) -- "ND" 0x4E44
  | underlyingPurgeNotificationMessage (message : UnderlyingPurgeNotificationMessage) -- "NU" 0x4E55
  | marketReentryNotificationMessage (message : MarketReentryNotificationMessage) -- "NR" 0x4E52
  deriving DecidableEq, Repr

namespace ServerUnsequencedMessage

/-- The Server Unsequenced Message Type each message is sent under -/
def tag : ServerUnsequencedMessage → BitVec 16
  | .notificationSubscriptionReplyMessage _ => 16738
  | .addComplexInstrumentReplyMessage _ => 16739
  | .mmParameterDefinitionReplyMessage _ => 16741
  | .activeQpSelfReplenishmentSetLimitReplyMessage _ => 16743
  | .quoteBlockReplyMessage _ => 20819
  | .detailedQuoteBlockReplyMessage _ => 20851
  | .underlyingPurgeReplyMessage _ => 20594
  | .marketReentryReplyMessage _ => 21074
  | .activeQpSelfReplenishmentRequestReentryReplyMessage _ => 21095
  | .auctionNotificationMessage _ => 20033
  | .instrumentPurgeNotificationMessage _ => 20036
  | .underlyingPurgeNotificationMessage _ => 20053
  | .marketReentryNotificationMessage _ => 20050

def encode : ServerUnsequencedMessage → List UInt8
  | .notificationSubscriptionReplyMessage message => NotificationSubscriptionReplyMessage.encode message
  | .addComplexInstrumentReplyMessage message => AddComplexInstrumentReplyMessage.encode message
  | .mmParameterDefinitionReplyMessage message => MmParameterDefinitionReplyMessage.encode message
  | .activeQpSelfReplenishmentSetLimitReplyMessage message => ActiveQpSelfReplenishmentSetLimitReplyMessage.encode message
  | .quoteBlockReplyMessage message => QuoteBlockReplyMessage.encode message
  | .detailedQuoteBlockReplyMessage message => DetailedQuoteBlockReplyMessage.encode message
  | .underlyingPurgeReplyMessage message => UnderlyingPurgeReplyMessage.encode message
  | .marketReentryReplyMessage message => MarketReentryReplyMessage.encode message
  | .activeQpSelfReplenishmentRequestReentryReplyMessage message => ActiveQpSelfReplenishmentRequestReentryReplyMessage.encode message
  | .auctionNotificationMessage message => AuctionNotificationMessage.encode message
  | .instrumentPurgeNotificationMessage message => InstrumentPurgeNotificationMessage.encode message
  | .underlyingPurgeNotificationMessage message => UnderlyingPurgeNotificationMessage.encode message
  | .marketReentryNotificationMessage message => MarketReentryNotificationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerUnsequencedMessage) : (encode message).length ≤ 1638400 := by
  cases message with
  | notificationSubscriptionReplyMessage inner =>
    simp only [encode, NotificationSubscriptionReplyMessage.encode_length]
    omega
  | addComplexInstrumentReplyMessage inner =>
    simp only [encode, AddComplexInstrumentReplyMessage.encode_length]
    omega
  | mmParameterDefinitionReplyMessage inner =>
    simp only [encode, MmParameterDefinitionReplyMessage.encode_length]
    omega
  | activeQpSelfReplenishmentSetLimitReplyMessage inner =>
    simp only [encode, ActiveQpSelfReplenishmentSetLimitReplyMessage.encode_length]
    omega
  | quoteBlockReplyMessage inner =>
    have bound_inner := QuoteBlockReplyMessage.encode_length_le inner
    simp only [encode]
    omega
  | detailedQuoteBlockReplyMessage inner =>
    have bound_inner := DetailedQuoteBlockReplyMessage.encode_length_le inner
    simp only [encode]
    omega
  | underlyingPurgeReplyMessage inner =>
    simp only [encode, UnderlyingPurgeReplyMessage.encode_length]
    omega
  | marketReentryReplyMessage inner =>
    simp only [encode, MarketReentryReplyMessage.encode_length]
    omega
  | activeQpSelfReplenishmentRequestReentryReplyMessage inner =>
    simp only [encode, ActiveQpSelfReplenishmentRequestReentryReplyMessage.encode_length]
    omega
  | auctionNotificationMessage inner =>
    have bound_inner := AuctionNotificationMessage.encode_length_le inner
    simp only [encode]
    omega
  | instrumentPurgeNotificationMessage inner =>
    simp only [encode, InstrumentPurgeNotificationMessage.encode_length]
    omega
  | underlyingPurgeNotificationMessage inner =>
    simp only [encode, UnderlyingPurgeNotificationMessage.encode_length]
    omega
  | marketReentryNotificationMessage inner =>
    simp only [encode, MarketReentryNotificationMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ServerUnsequencedMessage × List UInt8) :=
  if tag = 16738 then (NotificationSubscriptionReplyMessage.decode bytes).map fun (message, rest) => (.notificationSubscriptionReplyMessage message, rest)
  else if tag = 16739 then (AddComplexInstrumentReplyMessage.decode bytes).map fun (message, rest) => (.addComplexInstrumentReplyMessage message, rest)
  else if tag = 16741 then (MmParameterDefinitionReplyMessage.decode bytes).map fun (message, rest) => (.mmParameterDefinitionReplyMessage message, rest)
  else if tag = 16743 then (ActiveQpSelfReplenishmentSetLimitReplyMessage.decode bytes).map fun (message, rest) => (.activeQpSelfReplenishmentSetLimitReplyMessage message, rest)
  else if tag = 20819 then (QuoteBlockReplyMessage.decode bytes).map fun (message, rest) => (.quoteBlockReplyMessage message, rest)
  else if tag = 20851 then (DetailedQuoteBlockReplyMessage.decode bytes).map fun (message, rest) => (.detailedQuoteBlockReplyMessage message, rest)
  else if tag = 20594 then (UnderlyingPurgeReplyMessage.decode bytes).map fun (message, rest) => (.underlyingPurgeReplyMessage message, rest)
  else if tag = 21074 then (MarketReentryReplyMessage.decode bytes).map fun (message, rest) => (.marketReentryReplyMessage message, rest)
  else if tag = 21095 then (ActiveQpSelfReplenishmentRequestReentryReplyMessage.decode bytes).map fun (message, rest) => (.activeQpSelfReplenishmentRequestReentryReplyMessage message, rest)
  else if tag = 20033 then (AuctionNotificationMessage.decode bytes).map fun (message, rest) => (.auctionNotificationMessage message, rest)
  else if tag = 20036 then (InstrumentPurgeNotificationMessage.decode bytes).map fun (message, rest) => (.instrumentPurgeNotificationMessage message, rest)
  else if tag = 20053 then (UnderlyingPurgeNotificationMessage.decode bytes).map fun (message, rest) => (.underlyingPurgeNotificationMessage message, rest)
  else if tag = 20050 then (MarketReentryNotificationMessage.decode bytes).map fun (message, rest) => (.marketReentryNotificationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ServerUnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerUnsequencedMessage

/-- Server Unsequenced Data Packet -/
structure ServerUnsequencedDataPacket where
  serverUnsequencedMessage : ServerUnsequencedMessage
  deriving DecidableEq, Repr

namespace ServerUnsequencedDataPacket

def encode (message : ServerUnsequencedDataPacket) : List UInt8 :=
  encodeUInt 2 (ServerUnsequencedMessage.tag message.serverUnsequencedMessage)
    ++ (ServerUnsequencedMessage.encode message.serverUnsequencedMessage)

def decode (bytes : List UInt8) : Option (ServerUnsequencedDataPacket × List UInt8) := do
  let (serverUnsequencedMessageType, bytes) ← decodeUInt 2 bytes
  let (serverUnsequencedMessage, bytes) ← ServerUnsequencedMessage.decode serverUnsequencedMessageType bytes
  pure ({ serverUnsequencedMessage }, bytes)

theorem encode_length_pos (message : ServerUnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ServerUnsequencedDataPacket) : (encode message).length ≤ 1638402 := by
  unfold encode
  cases message.serverUnsequencedMessage with
  | notificationSubscriptionReplyMessage inner =>
    simp only [ServerUnsequencedMessage.encode, List.length_append, encodeUInt_length, NotificationSubscriptionReplyMessage.encode_length]
    omega
  | addComplexInstrumentReplyMessage inner =>
    simp only [ServerUnsequencedMessage.encode, List.length_append, encodeUInt_length, AddComplexInstrumentReplyMessage.encode_length]
    omega
  | mmParameterDefinitionReplyMessage inner =>
    simp only [ServerUnsequencedMessage.encode, List.length_append, encodeUInt_length, MmParameterDefinitionReplyMessage.encode_length]
    omega
  | activeQpSelfReplenishmentSetLimitReplyMessage inner =>
    simp only [ServerUnsequencedMessage.encode, List.length_append, encodeUInt_length, ActiveQpSelfReplenishmentSetLimitReplyMessage.encode_length]
    omega
  | quoteBlockReplyMessage inner =>
    have bound_inner := QuoteBlockReplyMessage.encode_length_le inner
    simp only [ServerUnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | detailedQuoteBlockReplyMessage inner =>
    have bound_inner := DetailedQuoteBlockReplyMessage.encode_length_le inner
    simp only [ServerUnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | underlyingPurgeReplyMessage inner =>
    simp only [ServerUnsequencedMessage.encode, List.length_append, encodeUInt_length, UnderlyingPurgeReplyMessage.encode_length]
    omega
  | marketReentryReplyMessage inner =>
    simp only [ServerUnsequencedMessage.encode, List.length_append, encodeUInt_length, MarketReentryReplyMessage.encode_length]
    omega
  | activeQpSelfReplenishmentRequestReentryReplyMessage inner =>
    simp only [ServerUnsequencedMessage.encode, List.length_append, encodeUInt_length, ActiveQpSelfReplenishmentRequestReentryReplyMessage.encode_length]
    omega
  | auctionNotificationMessage inner =>
    have bound_inner := AuctionNotificationMessage.encode_length_le inner
    simp only [ServerUnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | instrumentPurgeNotificationMessage inner =>
    simp only [ServerUnsequencedMessage.encode, List.length_append, encodeUInt_length, InstrumentPurgeNotificationMessage.encode_length]
    omega
  | underlyingPurgeNotificationMessage inner =>
    simp only [ServerUnsequencedMessage.encode, List.length_append, encodeUInt_length, UnderlyingPurgeNotificationMessage.encode_length]
    omega
  | marketReentryNotificationMessage inner =>
    simp only [ServerUnsequencedMessage.encode, List.length_append, encodeUInt_length, MarketReentryNotificationMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ServerUnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerUnsequencedMessage.decode_encode, some_bind]
  rfl

end ServerUnsequencedDataPacket

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
  | serverUnsequencedDataPacket (message : ServerUnsequencedDataPacket) -- "U" 0x55
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
  | .serverUnsequencedDataPacket _ => 85
  | .serverHeartbeatPacket _ => 72
  | .endOfSessionPacket _ => 90

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .serverUnsequencedDataPacket message => ServerUnsequencedDataPacket.encode message
  | .serverHeartbeatPacket message => ServerHeartbeatPacket.encode message
  | .endOfSessionPacket message => EndOfSessionPacket.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 1638402 := by
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
  | serverUnsequencedDataPacket inner =>
    have bound_inner := ServerUnsequencedDataPacket.encode_length_le inner
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
  else if tag = 85 then (ServerUnsequencedDataPacket.decode bytes).map fun (message, rest) => (.serverUnsequencedDataPacket message, rest)
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

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (ServerSoupBinTcpPacket × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ServerSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
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

end Omi.NasdaqMrxoptionsQuotingSqfV90Server
