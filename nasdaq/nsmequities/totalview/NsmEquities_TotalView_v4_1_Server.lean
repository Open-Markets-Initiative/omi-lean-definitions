import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) TotalView Itch v4.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesTotalviewItchV41Server

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
  [0x4F, 0x53, 0x51, 0x4D, 0x45, 0x43, 0x41, 0x52, 0x42]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfMarketHours -- Start Of Market Hours
  | endOfMarketHours -- End Of Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | emergencyMarketConditionHalt -- Emergency Market Condition Halt
  | emergencyMarketConditionQuoteOnlyPeriod -- Emergency Market Condition Quote Only Period
  | emergencyMarketConditionResumption -- Emergency Market Condition Resumption
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfMarketHours => 0x51
  | .endOfMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .emergencyMarketConditionHalt => 0x41
  | .emergencyMarketConditionQuoteOnlyPeriod => 0x52
  | .emergencyMarketConditionResumption => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x45 then .endOfSystemHours
  else if byte = 0x43 then .endOfMessages
  else if byte = 0x41 then .emergencyMarketConditionHalt
  else if byte = 0x52 then .emergencyMarketConditionQuoteOnlyPeriod
  else .emergencyMarketConditionResumption

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfMarketHours => decide
  | endOfMarketHours => decide
  | endOfSystemHours => decide
  | endOfMessages => decide
  | emergencyMarketConditionHalt => decide
  | emergencyMarketConditionQuoteOnlyPeriod => decide
  | emergencyMarketConditionResumption => decide
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

/-- Market Category: one byte code -/
def MarketCategory.codes : List UInt8 :=
  [0x4E, 0x41, 0x50, 0x51, 0x47, 0x53, 0x5A]

inductive MarketCategory where
  | nyse -- Nyse
  | amex -- Amex
  | arca -- Arca
  | nasdaqGsm -- Nasdaq Gsm
  | nasdaqGm -- Nasdaq Gm
  | nasdaqCm -- Nasdaq Cm
  | bats -- Bats
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCategory

def toByte : MarketCategory → UInt8
  | .nyse => 0x4E
  | .amex => 0x41
  | .arca => 0x50
  | .nasdaqGsm => 0x51
  | .nasdaqGm => 0x47
  | .nasdaqCm => 0x53
  | .bats => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCategory :=
  if byte = 0x4E then .nyse
  else if byte = 0x41 then .amex
  else if byte = 0x50 then .arca
  else if byte = 0x51 then .nasdaqGsm
  else if byte = 0x47 then .nasdaqGm
  else if byte = 0x53 then .nasdaqCm
  else .bats

def ofByte (byte : UInt8) : MarketCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCategory) : ofByte value.toByte = value := by
  cases value with
  | nyse => decide
  | amex => decide
  | arca => decide
  | nasdaqGsm => decide
  | nasdaqGm => decide
  | nasdaqCm => decide
  | bats => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCategory

/-- Financial Status Indicator: one byte code -/
def FinancialStatusIndicator.codes : List UInt8 :=
  [0x44, 0x45, 0x51, 0x53, 0x47, 0x48, 0x4A, 0x4B, 0x20]

inductive FinancialStatusIndicator where
  | deficient -- Deficient
  | delinquent -- Delinquent
  | bankrupt -- Bankrupt
  | suspended -- Suspended
  | deficientAndBankrupt -- Deficient And Bankrupt
  | deficientAndDelinquent -- Deficient And Delinquent
  | delinquentAndBankrupt -- Delinquent And Bankrupt
  | deficientDelinquentAndBankrupt -- Deficient Delinquent And Bankrupt
  | inCompliance -- In Compliance
  | unlisted (byte : { byte : UInt8 // byte ∉ FinancialStatusIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinancialStatusIndicator

def toByte : FinancialStatusIndicator → UInt8
  | .deficient => 0x44
  | .delinquent => 0x45
  | .bankrupt => 0x51
  | .suspended => 0x53
  | .deficientAndBankrupt => 0x47
  | .deficientAndDelinquent => 0x48
  | .delinquentAndBankrupt => 0x4A
  | .deficientDelinquentAndBankrupt => 0x4B
  | .inCompliance => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinancialStatusIndicator :=
  if byte = 0x44 then .deficient
  else if byte = 0x45 then .delinquent
  else if byte = 0x51 then .bankrupt
  else if byte = 0x53 then .suspended
  else if byte = 0x47 then .deficientAndBankrupt
  else if byte = 0x48 then .deficientAndDelinquent
  else if byte = 0x4A then .delinquentAndBankrupt
  else if byte = 0x4B then .deficientDelinquentAndBankrupt
  else .inCompliance

def ofByte (byte : UInt8) : FinancialStatusIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinancialStatusIndicator) : ofByte value.toByte = value := by
  cases value with
  | deficient => decide
  | delinquent => decide
  | bankrupt => decide
  | suspended => decide
  | deficientAndBankrupt => decide
  | deficientAndDelinquent => decide
  | delinquentAndBankrupt => decide
  | deficientDelinquentAndBankrupt => decide
  | inCompliance => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FinancialStatusIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinancialStatusIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FinancialStatusIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FinancialStatusIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FinancialStatusIndicator

/-- Round Lots Only: one byte code -/
def RoundLotsOnly.codes : List UInt8 :=
  [0x59, 0x4E]

inductive RoundLotsOnly where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ RoundLotsOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RoundLotsOnly

def toByte : RoundLotsOnly → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RoundLotsOnly :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : RoundLotsOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RoundLotsOnly) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RoundLotsOnly) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RoundLotsOnly × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RoundLotsOnly) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RoundLotsOnly) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RoundLotsOnly

/-- Trading State: one byte code -/
def TradingState.codes : List UInt8 :=
  [0x48, 0x50, 0x51, 0x54]

inductive TradingState where
  | halted -- Halted
  | paused -- Paused
  | quotationOnly -- Quotation Only
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .halted => 0x48
  | .paused => 0x50
  | .quotationOnly => 0x51
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x48 then .halted
  else if byte = 0x50 then .paused
  else if byte = 0x51 then .quotationOnly
  else .trading

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | paused => decide
  | quotationOnly => decide
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

/-- Reg Sho Action: one byte code -/
def RegShoAction.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive RegShoAction where
  | noPrice -- No Price
  | regShoShortSalePriceTestRestriction -- Reg Sho Short Sale Price Test Restriction
  | regShoShortSalePriceTest -- Reg Sho Short Sale Price Test
  | unlisted (byte : { byte : UInt8 // byte ∉ RegShoAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RegShoAction

def toByte : RegShoAction → UInt8
  | .noPrice => 0x30
  | .regShoShortSalePriceTestRestriction => 0x31
  | .regShoShortSalePriceTest => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RegShoAction :=
  if byte = 0x30 then .noPrice
  else if byte = 0x31 then .regShoShortSalePriceTestRestriction
  else .regShoShortSalePriceTest

def ofByte (byte : UInt8) : RegShoAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RegShoAction) : ofByte value.toByte = value := by
  cases value with
  | noPrice => decide
  | regShoShortSalePriceTestRestriction => decide
  | regShoShortSalePriceTest => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RegShoAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RegShoAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RegShoAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RegShoAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RegShoAction

/-- Primary Market Maker: one byte code -/
def PrimaryMarketMaker.codes : List UInt8 :=
  [0x59, 0x4E]

inductive PrimaryMarketMaker where
  | primary -- Primary
  | nonPrimary -- Non Primary
  | unlisted (byte : { byte : UInt8 // byte ∉ PrimaryMarketMaker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrimaryMarketMaker

def toByte : PrimaryMarketMaker → UInt8
  | .primary => 0x59
  | .nonPrimary => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrimaryMarketMaker :=
  if byte = 0x59 then .primary
  else .nonPrimary

def ofByte (byte : UInt8) : PrimaryMarketMaker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrimaryMarketMaker) : ofByte value.toByte = value := by
  cases value with
  | primary => decide
  | nonPrimary => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrimaryMarketMaker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrimaryMarketMaker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrimaryMarketMaker) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrimaryMarketMaker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrimaryMarketMaker

/-- Market Maker Mode: one byte code -/
def MarketMakerMode.codes : List UInt8 :=
  [0x4E, 0x50, 0x53, 0x52, 0x4C]

inductive MarketMakerMode where
  | normal -- Normal
  | passive -- Passive
  | syndicate -- Syndicate
  | preSyndicate -- Pre Syndicate
  | penalty -- Penalty
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketMakerMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketMakerMode

def toByte : MarketMakerMode → UInt8
  | .normal => 0x4E
  | .passive => 0x50
  | .syndicate => 0x53
  | .preSyndicate => 0x52
  | .penalty => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketMakerMode :=
  if byte = 0x4E then .normal
  else if byte = 0x50 then .passive
  else if byte = 0x53 then .syndicate
  else if byte = 0x52 then .preSyndicate
  else .penalty

def ofByte (byte : UInt8) : MarketMakerMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketMakerMode) : ofByte value.toByte = value := by
  cases value with
  | normal => decide
  | passive => decide
  | syndicate => decide
  | preSyndicate => decide
  | penalty => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketMakerMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketMakerMode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketMakerMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketMakerMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketMakerMode

/-- Market Participant State: one byte code -/
def MarketParticipantState.codes : List UInt8 :=
  [0x41, 0x45, 0x57, 0x53, 0x44]

inductive MarketParticipantState where
  | active -- Active
  | excusedWithdrawn -- Excused Withdrawn
  | withdrawn -- Withdrawn
  | suspended -- Suspended
  | deleted -- Deleted
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketParticipantState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketParticipantState

def toByte : MarketParticipantState → UInt8
  | .active => 0x41
  | .excusedWithdrawn => 0x45
  | .withdrawn => 0x57
  | .suspended => 0x53
  | .deleted => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketParticipantState :=
  if byte = 0x41 then .active
  else if byte = 0x45 then .excusedWithdrawn
  else if byte = 0x57 then .withdrawn
  else if byte = 0x53 then .suspended
  else .deleted

def ofByte (byte : UInt8) : MarketParticipantState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketParticipantState) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | excusedWithdrawn => decide
  | withdrawn => decide
  | suspended => decide
  | deleted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketParticipantState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketParticipantState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketParticipantState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketParticipantState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketParticipantState

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

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x4F, 0x43, 0x48, 0x49]

inductive CrossType where
  | opening -- Opening
  | closing -- Closing
  | crossForIpoAndHalted -- Cross For Ipo And Halted
  | nasdaqCrossNetwork -- Nasdaq Cross Network
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .opening => 0x4F
  | .closing => 0x43
  | .crossForIpoAndHalted => 0x48
  | .nasdaqCrossNetwork => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4F then .opening
  else if byte = 0x43 then .closing
  else if byte = 0x48 then .crossForIpoAndHalted
  else .nasdaqCrossNetwork

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | opening => decide
  | closing => decide
  | crossForIpoAndHalted => decide
  | nasdaqCrossNetwork => decide
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

/-- Imbalance Direction: one byte code -/
def ImbalanceDirection.codes : List UInt8 :=
  [0x42, 0x53, 0x4E, 0x4F]

inductive ImbalanceDirection where
  | buy -- Buy
  | sell -- Sell
  | no -- No
  | insufficientOrders -- Insufficient Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceDirection

def toByte : ImbalanceDirection → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .no => 0x4E
  | .insufficientOrders => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceDirection :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x4E then .no
  else .insufficientOrders

def ofByte (byte : UInt8) : ImbalanceDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceDirection) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | no => decide
  | insufficientOrders => decide
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

/-- Price Variation Indicator: one byte code -/
def PriceVariationIndicator.codes : List UInt8 :=
  [0x4C, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x20]

inductive PriceVariationIndicator where
  | less -- Less
  | oneToOnePointNineNinePercent -- One To One Point Nine Nine Percent
  | twoToTwoPointNineNinePercent -- Two To Two Point Nine Nine Percent
  | threeToThreePointNineNinePercent -- Three To Three Point Nine Nine Percent
  | fourToFourPointNineNinePercent -- Four To Four Point Nine Nine Percent
  | fiveToFivePointNineNinePercent -- Five To Five Point Nine Nine Percent
  | sixToSixPointNineNinePercent -- Six To Six Point Nine Nine Percent
  | sevenToSevenPointNineNinePercent -- Seven To Seven Point Nine Nine Percent
  | eightToEightPointNineNinePercent -- Eight To Eight Point Nine Nine Percent
  | nineToNinePointNineNinePercent -- Nine To Nine Point Nine Nine Percent
  | tenToNineteenPointNineNinePercent -- Ten To Nineteen Point Nine Nine Percent
  | twentyToTwentyNinePointNineNinePercent -- Twenty To Twenty Nine Point Nine Nine Percent
  | thirtyPercentOrGreater -- Thirty Percent Or Greater
  | noCalculation -- No Calculation
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceVariationIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceVariationIndicator

def toByte : PriceVariationIndicator → UInt8
  | .less => 0x4C
  | .oneToOnePointNineNinePercent => 0x31
  | .twoToTwoPointNineNinePercent => 0x32
  | .threeToThreePointNineNinePercent => 0x33
  | .fourToFourPointNineNinePercent => 0x34
  | .fiveToFivePointNineNinePercent => 0x35
  | .sixToSixPointNineNinePercent => 0x36
  | .sevenToSevenPointNineNinePercent => 0x37
  | .eightToEightPointNineNinePercent => 0x38
  | .nineToNinePointNineNinePercent => 0x39
  | .tenToNineteenPointNineNinePercent => 0x41
  | .twentyToTwentyNinePointNineNinePercent => 0x42
  | .thirtyPercentOrGreater => 0x43
  | .noCalculation => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceVariationIndicator :=
  if byte = 0x4C then .less
  else if byte = 0x31 then .oneToOnePointNineNinePercent
  else if byte = 0x32 then .twoToTwoPointNineNinePercent
  else if byte = 0x33 then .threeToThreePointNineNinePercent
  else if byte = 0x34 then .fourToFourPointNineNinePercent
  else if byte = 0x35 then .fiveToFivePointNineNinePercent
  else if byte = 0x36 then .sixToSixPointNineNinePercent
  else if byte = 0x37 then .sevenToSevenPointNineNinePercent
  else if byte = 0x38 then .eightToEightPointNineNinePercent
  else if byte = 0x39 then .nineToNinePointNineNinePercent
  else if byte = 0x41 then .tenToNineteenPointNineNinePercent
  else if byte = 0x42 then .twentyToTwentyNinePointNineNinePercent
  else if byte = 0x43 then .thirtyPercentOrGreater
  else .noCalculation

def ofByte (byte : UInt8) : PriceVariationIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceVariationIndicator) : ofByte value.toByte = value := by
  cases value with
  | less => decide
  | oneToOnePointNineNinePercent => decide
  | twoToTwoPointNineNinePercent => decide
  | threeToThreePointNineNinePercent => decide
  | fourToFourPointNineNinePercent => decide
  | fiveToFivePointNineNinePercent => decide
  | sixToSixPointNineNinePercent => decide
  | sevenToSevenPointNineNinePercent => decide
  | eightToEightPointNineNinePercent => decide
  | nineToNinePointNineNinePercent => decide
  | tenToNineteenPointNineNinePercent => decide
  | twentyToTwentyNinePointNineNinePercent => decide
  | thirtyPercentOrGreater => decide
  | noCalculation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceVariationIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceVariationIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceVariationIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceVariationIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceVariationIndicator

/-- Interest Flag: one byte code -/
def InterestFlag.codes : List UInt8 :=
  [0x42, 0x53, 0x41, 0x4E]

inductive InterestFlag where
  | rpiBuy -- Rpi Buy
  | rpiSell -- Rpi Sell
  | rpiBoth -- Rpi Both
  | noRpi -- No Rpi
  | unlisted (byte : { byte : UInt8 // byte ∉ InterestFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InterestFlag

def toByte : InterestFlag → UInt8
  | .rpiBuy => 0x42
  | .rpiSell => 0x53
  | .rpiBoth => 0x41
  | .noRpi => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InterestFlag :=
  if byte = 0x42 then .rpiBuy
  else if byte = 0x53 then .rpiSell
  else if byte = 0x41 then .rpiBoth
  else .noRpi

def ofByte (byte : UInt8) : InterestFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InterestFlag) : ofByte value.toByte = value := by
  cases value with
  | rpiBuy => decide
  | rpiSell => decide
  | rpiBoth => decide
  | noRpi => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InterestFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InterestFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InterestFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InterestFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InterestFlag

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

/-- Timestamp Message: 4 bytes -/
structure TimestampMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace TimestampMessage

def encode (message : TimestampMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (TimestampMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : TimestampMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : TimestampMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimestampMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TimestampMessage

/-- System Event Message: 5 bytes -/
structure SystemEventMessage where
  nanoseconds : BitVec 32
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (EventCode.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ nanoseconds, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 5 := by
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
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Stock Directory Message: 19 bytes -/
structure StockDirectoryMessage where
  nanoseconds : BitVec 32
  stock : Alpha 8
  marketCategory : MarketCategory
  financialStatusIndicator : FinancialStatusIndicator
  roundLotSize : BitVec 32
  roundLotsOnly : RoundLotsOnly
  deriving DecidableEq, Repr

namespace StockDirectoryMessage

def encode (message : StockDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.stock
    ++ (MarketCategory.encode message.marketCategory
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (encodeUInt 4 message.roundLotSize
    ++ (RoundLotsOnly.encode message.roundLotsOnly)))))

def decode (bytes : List UInt8) : Option (StockDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (marketCategory, bytes) ← MarketCategory.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (roundLotsOnly, bytes) ← RoundLotsOnly.decode bytes
  pure ({ nanoseconds, stock, marketCategory, financialStatusIndicator, roundLotSize, roundLotsOnly }, bytes)

@[simp] theorem encode_length (message : StockDirectoryMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, MarketCategory.encode_length, FinancialStatusIndicator.encode_length, RoundLotsOnly.encode_length]

theorem encode_length_pos (message : StockDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [RoundLotsOnly.decode_encode, some_bind]
  rfl

end StockDirectoryMessage

/-- Stock Trading Action Message: 18 bytes -/
structure StockTradingActionMessage where
  nanoseconds : BitVec 32
  stock : Alpha 8
  tradingState : TradingState
  reserved : Alpha 1
  reason : Alpha 4
  deriving DecidableEq, Repr

namespace StockTradingActionMessage

def encode (message : StockTradingActionMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.stock
    ++ (TradingState.encode message.tradingState
    ++ (Alpha.encode message.reserved
    ++ (Alpha.encode message.reason))))

def decode (bytes : List UInt8) : Option (StockTradingActionMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (reason, bytes) ← Alpha.decode 4 bytes
  pure ({ nanoseconds, stock, tradingState, reserved, reason }, bytes)

@[simp] theorem encode_length (message : StockTradingActionMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradingState.encode_length]

theorem encode_length_pos (message : StockTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockTradingActionMessage

/-- Reg Sho Short Sale Price Test Restricted Indicator Message: 13 bytes -/
structure RegShoShortSalePriceTestRestrictedIndicatorMessage where
  nanoseconds : BitVec 32
  stock : Alpha 8
  regShoAction : RegShoAction
  deriving DecidableEq, Repr

namespace RegShoShortSalePriceTestRestrictedIndicatorMessage

def encode (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.stock
    ++ (RegShoAction.encode message.regShoAction))

def decode (bytes : List UInt8) : Option (RegShoShortSalePriceTestRestrictedIndicatorMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (regShoAction, bytes) ← RegShoAction.decode bytes
  pure ({ nanoseconds, stock, regShoAction }, bytes)

@[simp] theorem encode_length (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, RegShoAction.encode_length]

theorem encode_length_pos (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RegShoAction.decode_encode, some_bind]
  rfl

end RegShoShortSalePriceTestRestrictedIndicatorMessage

/-- Market Participant Position Message: 19 bytes -/
structure MarketParticipantPositionMessage where
  nanoseconds : BitVec 32
  mpid : Alpha 4
  stock : Alpha 8
  primaryMarketMaker : PrimaryMarketMaker
  marketMakerMode : MarketMakerMode
  marketParticipantState : MarketParticipantState
  deriving DecidableEq, Repr

namespace MarketParticipantPositionMessage

def encode (message : MarketParticipantPositionMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.stock
    ++ (PrimaryMarketMaker.encode message.primaryMarketMaker
    ++ (MarketMakerMode.encode message.marketMakerMode
    ++ (MarketParticipantState.encode message.marketParticipantState)))))

def decode (bytes : List UInt8) : Option (MarketParticipantPositionMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (primaryMarketMaker, bytes) ← PrimaryMarketMaker.decode bytes
  let (marketMakerMode, bytes) ← MarketMakerMode.decode bytes
  let (marketParticipantState, bytes) ← MarketParticipantState.decode bytes
  pure ({ nanoseconds, mpid, stock, primaryMarketMaker, marketMakerMode, marketParticipantState }, bytes)

@[simp] theorem encode_length (message : MarketParticipantPositionMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, PrimaryMarketMaker.encode_length, MarketMakerMode.encode_length, MarketParticipantState.encode_length]

theorem encode_length_pos (message : MarketParticipantPositionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketParticipantPositionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryMarketMaker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMakerMode.decode_encode, some_bind]
  dsimp only
  rw [MarketParticipantState.decode_encode, some_bind]
  rfl

end MarketParticipantPositionMessage

/-- Add Order Message: 29 bytes -/
structure AddOrderMessage where
  nanoseconds : BitVec 32
  orderReferenceNumber : BitVec 64
  side : Side
  shares : BitVec 32
  stock : Alpha 8
  price : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.shares
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 4 message.price)))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderReferenceNumber, side, shares, stock, price }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length]

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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessage

/-- Add Order With Mpid Message: 33 bytes -/
structure AddOrderWithMpidMessage where
  nanoseconds : BitVec 32
  orderReferenceNumber : BitVec 64
  side : Side
  shares : BitVec 32
  stock : Alpha 8
  price : BitVec 32
  attribution : Alpha 4
  deriving DecidableEq, Repr

namespace AddOrderWithMpidMessage

def encode (message : AddOrderWithMpidMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.shares
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 4 message.price
    ++ (Alpha.encode message.attribution))))))

def decode (bytes : List UInt8) : Option (AddOrderWithMpidMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (attribution, bytes) ← Alpha.decode 4 bytes
  pure ({ nanoseconds, orderReferenceNumber, side, shares, stock, price, attribution }, bytes)

@[simp] theorem encode_length (message : AddOrderWithMpidMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderWithMpidMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderWithMpidMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderWithMpidMessage

/-- Order Executed Message: 24 bytes -/
structure OrderExecutedMessage where
  nanoseconds : BitVec 32
  orderReferenceNumber : BitVec 64
  executedShares : BitVec 32
  matchNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeUInt 4 message.executedShares
    ++ (encodeUInt 8 message.matchNumber)))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (executedShares, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, orderReferenceNumber, executedShares, matchNumber }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
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

end OrderExecutedMessage

/-- Order Executed With Price Message: 29 bytes -/
structure OrderExecutedWithPriceMessage where
  nanoseconds : BitVec 32
  orderReferenceNumber : BitVec 64
  executedShares : BitVec 32
  matchNumber : BitVec 64
  printable : Printable
  executionPrice : BitVec 32
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeUInt 4 message.executedShares
    ++ (encodeUInt 8 message.matchNumber
    ++ (Printable.encode message.printable
    ++ (encodeUInt 4 message.executionPrice)))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (executedShares, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderReferenceNumber, executedShares, matchNumber, printable := printable_, executionPrice }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length]

theorem encode_length_pos (message : OrderExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedWithPriceMessage

/-- Order Cancel Message: 16 bytes -/
structure OrderCancelMessage where
  nanoseconds : BitVec 32
  orderReferenceNumber : BitVec 64
  canceledShares : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeUInt 4 message.canceledShares))

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (canceledShares, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderReferenceNumber, canceledShares }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 16 := by
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderCancelMessage

/-- Order Delete Message: 12 bytes -/
structure OrderDeleteMessage where
  nanoseconds : BitVec 32
  orderReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderReferenceNumber)

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, orderReferenceNumber }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDeleteMessage

/-- Order Replace Message: 28 bytes -/
structure OrderReplaceMessage where
  nanoseconds : BitVec 32
  originalOrderReferenceNumber : BitVec 64
  newOrderReferenceNumber : BitVec 64
  shares : BitVec 32
  price : BitVec 32
  deriving DecidableEq, Repr

namespace OrderReplaceMessage

def encode (message : OrderReplaceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.originalOrderReferenceNumber
    ++ (encodeUInt 8 message.newOrderReferenceNumber
    ++ (encodeUInt 4 message.shares
    ++ (encodeUInt 4 message.price))))

def decode (bytes : List UInt8) : Option (OrderReplaceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (originalOrderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (newOrderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, originalOrderReferenceNumber, newOrderReferenceNumber, shares, price }, bytes)

@[simp] theorem encode_length (message : OrderReplaceMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderReplaceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceMessage) (rest : List UInt8) :
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

end OrderReplaceMessage

/-- Trade Message: 37 bytes -/
structure TradeMessage where
  nanoseconds : BitVec 32
  orderReferenceNumber : BitVec 64
  side : Side
  shares : BitVec 32
  stock : Alpha 8
  price : BitVec 32
  matchNumber : BitVec 64
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.shares
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 8 message.matchNumber))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, orderReferenceNumber, side, shares, stock, price, matchNumber }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length]

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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeMessage

/-- Cross Trade Message: 33 bytes -/
structure CrossTradeMessage where
  nanoseconds : BitVec 32
  crossShares : BitVec 64
  stock : Alpha 8
  crossPrice : BitVec 32
  matchNumber : BitVec 64
  crossType : CrossType
  deriving DecidableEq, Repr

namespace CrossTradeMessage

def encode (message : CrossTradeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.crossShares
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 4 message.crossPrice
    ++ (encodeUInt 8 message.matchNumber
    ++ (CrossType.encode message.crossType)))))

def decode (bytes : List UInt8) : Option (CrossTradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (crossShares, bytes) ← decodeUInt 8 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (crossPrice, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  pure ({ nanoseconds, crossShares, stock, crossPrice, matchNumber, crossType }, bytes)

@[simp] theorem encode_length (message : CrossTradeMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, CrossType.encode_length]

theorem encode_length_pos (message : CrossTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossTradeMessage) (rest : List UInt8) :
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
  rw [CrossType.decode_encode, some_bind]
  rfl

end CrossTradeMessage

/-- Broken Trade Message: 12 bytes -/
structure BrokenTradeMessage where
  nanoseconds : BitVec 32
  matchNumber : BitVec 64
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.matchNumber)

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, matchNumber }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BrokenTradeMessage

/-- Net Order Imbalance Indicator Message: 43 bytes -/
structure NetOrderImbalanceIndicatorMessage where
  nanoseconds : BitVec 32
  pairedShares : BitVec 64
  imbalanceShares : BitVec 64
  imbalanceDirection : ImbalanceDirection
  stock : Alpha 8
  farPrice : BitVec 32
  nearPrice : BitVec 32
  currentReferencePrice : BitVec 32
  crossType : CrossType
  priceVariationIndicator : PriceVariationIndicator
  deriving DecidableEq, Repr

namespace NetOrderImbalanceIndicatorMessage

def encode (message : NetOrderImbalanceIndicatorMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.pairedShares
    ++ (encodeUInt 8 message.imbalanceShares
    ++ (ImbalanceDirection.encode message.imbalanceDirection
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 4 message.farPrice
    ++ (encodeUInt 4 message.nearPrice
    ++ (encodeUInt 4 message.currentReferencePrice
    ++ (CrossType.encode message.crossType
    ++ (PriceVariationIndicator.encode message.priceVariationIndicator)))))))))

def decode (bytes : List UInt8) : Option (NetOrderImbalanceIndicatorMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (pairedShares, bytes) ← decodeUInt 8 bytes
  let (imbalanceShares, bytes) ← decodeUInt 8 bytes
  let (imbalanceDirection, bytes) ← ImbalanceDirection.decode bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (farPrice, bytes) ← decodeUInt 4 bytes
  let (nearPrice, bytes) ← decodeUInt 4 bytes
  let (currentReferencePrice, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (priceVariationIndicator, bytes) ← PriceVariationIndicator.decode bytes
  pure ({ nanoseconds, pairedShares, imbalanceShares, imbalanceDirection, stock, farPrice, nearPrice, currentReferencePrice, crossType, priceVariationIndicator }, bytes)

@[simp] theorem encode_length (message : NetOrderImbalanceIndicatorMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ImbalanceDirection.encode_length, Alpha.encode_length, CrossType.encode_length, PriceVariationIndicator.encode_length]

theorem encode_length_pos (message : NetOrderImbalanceIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetOrderImbalanceIndicatorMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [PriceVariationIndicator.decode_encode, some_bind]
  rfl

end NetOrderImbalanceIndicatorMessage

/-- Retail Price Improvement Indicator Message: 13 bytes -/
structure RetailPriceImprovementIndicatorMessage where
  nanoseconds : BitVec 32
  stock : Alpha 8
  interestFlag : InterestFlag
  deriving DecidableEq, Repr

namespace RetailPriceImprovementIndicatorMessage

def encode (message : RetailPriceImprovementIndicatorMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.stock
    ++ (InterestFlag.encode message.interestFlag))

def decode (bytes : List UInt8) : Option (RetailPriceImprovementIndicatorMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (interestFlag, bytes) ← InterestFlag.decode bytes
  pure ({ nanoseconds, stock, interestFlag }, bytes)

@[simp] theorem encode_length (message : RetailPriceImprovementIndicatorMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, InterestFlag.encode_length]

theorem encode_length_pos (message : RetailPriceImprovementIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetailPriceImprovementIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InterestFlag.decode_encode, some_bind]
  rfl

end RetailPriceImprovementIndicatorMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | timestampMessage (message : TimestampMessage) -- "T" 0x54
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | stockDirectoryMessage (message : StockDirectoryMessage) -- "R" 0x52
  | stockTradingActionMessage (message : StockTradingActionMessage) -- "H" 0x48
  | regShoShortSalePriceTestRestrictedIndicatorMessage (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) -- "Y" 0x59
  | marketParticipantPositionMessage (message : MarketParticipantPositionMessage) -- "L" 0x4C
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | addOrderWithMpidMessage (message : AddOrderWithMpidMessage) -- "F" 0x46
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- "C" 0x43
  | orderCancelMessage (message : OrderCancelMessage) -- "X" 0x58
  | orderDeleteMessage (message : OrderDeleteMessage) -- "D" 0x44
  | orderReplaceMessage (message : OrderReplaceMessage) -- "U" 0x55
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | crossTradeMessage (message : CrossTradeMessage) -- "Q" 0x51
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  | netOrderImbalanceIndicatorMessage (message : NetOrderImbalanceIndicatorMessage) -- "I" 0x49
  | retailPriceImprovementIndicatorMessage (message : RetailPriceImprovementIndicatorMessage) -- "N" 0x4E
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .timestampMessage _ => 84
  | .systemEventMessage _ => 83
  | .stockDirectoryMessage _ => 82
  | .stockTradingActionMessage _ => 72
  | .regShoShortSalePriceTestRestrictedIndicatorMessage _ => 89
  | .marketParticipantPositionMessage _ => 76
  | .addOrderMessage _ => 65
  | .addOrderWithMpidMessage _ => 70
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .orderCancelMessage _ => 88
  | .orderDeleteMessage _ => 68
  | .orderReplaceMessage _ => 85
  | .tradeMessage _ => 80
  | .crossTradeMessage _ => 81
  | .brokenTradeMessage _ => 66
  | .netOrderImbalanceIndicatorMessage _ => 73
  | .retailPriceImprovementIndicatorMessage _ => 78

def encode : SequencedMessage → List UInt8
  | .timestampMessage message => TimestampMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .stockDirectoryMessage message => StockDirectoryMessage.encode message
  | .stockTradingActionMessage message => StockTradingActionMessage.encode message
  | .regShoShortSalePriceTestRestrictedIndicatorMessage message => RegShoShortSalePriceTestRestrictedIndicatorMessage.encode message
  | .marketParticipantPositionMessage message => MarketParticipantPositionMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .addOrderWithMpidMessage message => AddOrderWithMpidMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderReplaceMessage message => OrderReplaceMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .crossTradeMessage message => CrossTradeMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .netOrderImbalanceIndicatorMessage message => NetOrderImbalanceIndicatorMessage.encode message
  | .retailPriceImprovementIndicatorMessage message => RetailPriceImprovementIndicatorMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 43 := by
  cases message with
  | timestampMessage inner =>
    simp only [encode, TimestampMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [encode, StockDirectoryMessage.encode_length]
    omega
  | stockTradingActionMessage inner =>
    simp only [encode, StockTradingActionMessage.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [encode, RegShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | marketParticipantPositionMessage inner =>
    simp only [encode, MarketParticipantPositionMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | addOrderWithMpidMessage inner =>
    simp only [encode, AddOrderWithMpidMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [encode, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [encode, OrderCancelMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [encode, OrderDeleteMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [encode, OrderReplaceMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | crossTradeMessage inner =>
    simp only [encode, CrossTradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega
  | netOrderImbalanceIndicatorMessage inner =>
    simp only [encode, NetOrderImbalanceIndicatorMessage.encode_length]
    omega
  | retailPriceImprovementIndicatorMessage inner =>
    simp only [encode, RetailPriceImprovementIndicatorMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 84 then (TimestampMessage.decode bytes).map fun (message, rest) => (.timestampMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (StockDirectoryMessage.decode bytes).map fun (message, rest) => (.stockDirectoryMessage message, rest)
  else if tag = 72 then (StockTradingActionMessage.decode bytes).map fun (message, rest) => (.stockTradingActionMessage message, rest)
  else if tag = 89 then (RegShoShortSalePriceTestRestrictedIndicatorMessage.decode bytes).map fun (message, rest) => (.regShoShortSalePriceTestRestrictedIndicatorMessage message, rest)
  else if tag = 76 then (MarketParticipantPositionMessage.decode bytes).map fun (message, rest) => (.marketParticipantPositionMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 70 then (AddOrderWithMpidMessage.decode bytes).map fun (message, rest) => (.addOrderWithMpidMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 88 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 85 then (OrderReplaceMessage.decode bytes).map fun (message, rest) => (.orderReplaceMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 81 then (CrossTradeMessage.decode bytes).map fun (message, rest) => (.crossTradeMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 73 then (NetOrderImbalanceIndicatorMessage.decode bytes).map fun (message, rest) => (.netOrderImbalanceIndicatorMessage message, rest)
  else if tag = 78 then (RetailPriceImprovementIndicatorMessage.decode bytes).map fun (message, rest) => (.retailPriceImprovementIndicatorMessage message, rest)
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
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 44 := by
  unfold encode
  cases message.sequencedMessage with
  | timestampMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TimestampMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, StockDirectoryMessage.encode_length]
    omega
  | stockTradingActionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, StockTradingActionMessage.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, RegShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | marketParticipantPositionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, MarketParticipantPositionMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | addOrderWithMpidMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderWithMpidMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderCancelMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderReplaceMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | crossTradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, CrossTradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | netOrderImbalanceIndicatorMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, NetOrderImbalanceIndicatorMessage.encode_length]
    omega
  | retailPriceImprovementIndicatorMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, RetailPriceImprovementIndicatorMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

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
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 44 := by
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
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).map fun (message, rest) => (.loginAcceptedPacket message, rest)
  else if tag = 74 then (LoginRejectedPacket.decode bytes).map fun (message, rest) => (.loginRejectedPacket message, rest)
  else if tag = 83 then (SequencedDataPacket.decode bytes).map fun (message, rest) => (.sequencedDataPacket message, rest)
  else if tag = 72 then (ServerHeartbeat.decode bytes).map fun (message, rest) => (.serverHeartbeat message, rest)
  else if tag = 90 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
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

end Omi.NasdaqNsmequitiesTotalviewItchV41Server
