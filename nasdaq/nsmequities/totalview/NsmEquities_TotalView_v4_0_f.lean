import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) TotalView Itch v4.0.f

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesTotalviewItchV40F

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
  [0x54, 0x51, 0x47, 0x53]

inductive MarketCategory where
  | cqs -- Cqs
  | nasdaqGlobalSelectMarket -- Nasdaq Global Select Market
  | nasdaqGlobalMarket -- Nasdaq Global Market
  | nasdaqCapitalMarket -- Nasdaq Capital Market
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCategory

def toByte : MarketCategory → UInt8
  | .cqs => 0x54
  | .nasdaqGlobalSelectMarket => 0x51
  | .nasdaqGlobalMarket => 0x47
  | .nasdaqCapitalMarket => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCategory :=
  if byte = 0x54 then .cqs
  else if byte = 0x51 then .nasdaqGlobalSelectMarket
  else if byte = 0x47 then .nasdaqGlobalMarket
  else .nasdaqCapitalMarket

def ofByte (byte : UInt8) : MarketCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCategory) : ofByte value.toByte = value := by
  cases value with
  | cqs => decide
  | nasdaqGlobalSelectMarket => decide
  | nasdaqGlobalMarket => decide
  | nasdaqCapitalMarket => decide
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
  | roundLotsOnly -- Round Lots Only
  | oddMixedLotsAllowed -- Odd Mixed Lots Allowed
  | unlisted (byte : { byte : UInt8 // byte ∉ RoundLotsOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RoundLotsOnly

def toByte : RoundLotsOnly → UInt8
  | .roundLotsOnly => 0x59
  | .oddMixedLotsAllowed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RoundLotsOnly :=
  if byte = 0x59 then .roundLotsOnly
  else .oddMixedLotsAllowed

def ofByte (byte : UInt8) : RoundLotsOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RoundLotsOnly) : ofByte value.toByte = value := by
  cases value with
  | roundLotsOnly => decide
  | oddMixedLotsAllowed => decide
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
  [0x48, 0x51, 0x54]

inductive TradingState where
  | halted -- Halted
  | quotationOnlyPeriod -- Quotation Only Period
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .halted => 0x48
  | .quotationOnlyPeriod => 0x51
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x48 then .halted
  else if byte = 0x51 then .quotationOnlyPeriod
  else .trading

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | quotationOnlyPeriod => decide
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

/-- Display: one byte code -/
def Display.codes : List UInt8 :=
  [0x59, 0x53]

inductive Display where
  | displayable -- Displayable
  | flash -- Flash
  | unlisted (byte : { byte : UInt8 // byte ∉ Display.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Display

def toByte : Display → UInt8
  | .displayable => 0x59
  | .flash => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Display :=
  if byte = 0x59 then .displayable
  else .flash

def ofByte (byte : UInt8) : Display :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Display) : ofByte value.toByte = value := by
  cases value with
  | displayable => decide
  | flash => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Display) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Display × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Display) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Display) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Display

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
  | ipoAndHalted -- Ipo And Halted
  | crossNetwork -- Cross Network
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .opening => 0x4F
  | .closing => 0x43
  | .ipoAndHalted => 0x48
  | .crossNetwork => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4F then .opening
  else if byte = 0x43 then .closing
  else if byte = 0x48 then .ipoAndHalted
  else .crossNetwork

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | opening => decide
  | closing => decide
  | ipoAndHalted => decide
  | crossNetwork => decide
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
  | noImbalance -- No Imbalance
  | insufficientOrders -- Insufficient Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceDirection

def toByte : ImbalanceDirection → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .noImbalance => 0x4E
  | .insufficientOrders => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceDirection :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x4E then .noImbalance
  else .insufficientOrders

def ofByte (byte : UInt8) : ImbalanceDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceDirection) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | noImbalance => decide
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
  | lessThanOnePercent -- Less Than One Percent
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
  | cannotBeCalculated -- Cannot Be Calculated
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceVariationIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceVariationIndicator

def toByte : PriceVariationIndicator → UInt8
  | .lessThanOnePercent => 0x4C
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
  | .cannotBeCalculated => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceVariationIndicator :=
  if byte = 0x4C then .lessThanOnePercent
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
  else .cannotBeCalculated

def ofByte (byte : UInt8) : PriceVariationIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceVariationIndicator) : ofByte value.toByte = value := by
  cases value with
  | lessThanOnePercent => decide
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
  | cannotBeCalculated => decide
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

/-- Stock Directory Message: 17 bytes -/
structure StockDirectoryMessage where
  nanoseconds : BitVec 32
  stock : Alpha 6
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
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (marketCategory, bytes) ← MarketCategory.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (roundLotsOnly_, bytes) ← RoundLotsOnly.decode bytes
  pure ({ nanoseconds, stock, marketCategory, financialStatusIndicator, roundLotSize, roundLotsOnly := roundLotsOnly_ }, bytes)

@[simp] theorem encode_length (message : StockDirectoryMessage) : (encode message).length = 17 := by
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

/-- Stock Trading Action Message: 16 bytes -/
structure StockTradingActionMessage where
  nanoseconds : BitVec 32
  stock : Alpha 6
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
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (reason, bytes) ← Alpha.decode 4 bytes
  pure ({ nanoseconds, stock, tradingState, reserved, reason }, bytes)

@[simp] theorem encode_length (message : StockTradingActionMessage) : (encode message).length = 16 := by
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

/-- Market Participant Position Message: 17 bytes -/
structure MarketParticipantPositionMessage where
  nanoseconds : BitVec 32
  mpid : Alpha 4
  stock : Alpha 6
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
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (primaryMarketMaker, bytes) ← PrimaryMarketMaker.decode bytes
  let (marketMakerMode, bytes) ← MarketMakerMode.decode bytes
  let (marketParticipantState, bytes) ← MarketParticipantState.decode bytes
  pure ({ nanoseconds, mpid, stock, primaryMarketMaker, marketMakerMode, marketParticipantState }, bytes)

@[simp] theorem encode_length (message : MarketParticipantPositionMessage) : (encode message).length = 17 := by
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

/-- Add Order Message: 28 bytes -/
structure AddOrderMessage where
  nanoseconds : BitVec 32
  orderReferenceNumber : BitVec 64
  side : Side
  shares : BitVec 32
  stock : Alpha 6
  price : BitVec 32
  display : Display
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.shares
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 4 message.price
    ++ (Display.encode message.display))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (display, bytes) ← Display.decode bytes
  pure ({ nanoseconds, orderReferenceNumber, side, shares, stock, price, display }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length, Display.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Display.decode_encode, some_bind]
  rfl

end AddOrderMessage

/-- Add Order With Mpid Message: 31 bytes -/
structure AddOrderWithMpidMessage where
  nanoseconds : BitVec 32
  orderReferenceNumber : BitVec 64
  side : Side
  shares : BitVec 32
  stock : Alpha 6
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
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (attribution, bytes) ← Alpha.decode 4 bytes
  pure ({ nanoseconds, orderReferenceNumber, side, shares, stock, price, attribution }, bytes)

@[simp] theorem encode_length (message : AddOrderWithMpidMessage) : (encode message).length = 31 := by
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

/-- Order Replace Message: 29 bytes -/
structure OrderReplaceMessage where
  nanoseconds : BitVec 32
  originalOrderReferenceNumber : BitVec 64
  newOrderReferenceNumber : BitVec 64
  shares : BitVec 32
  price : BitVec 32
  display : Display
  deriving DecidableEq, Repr

namespace OrderReplaceMessage

def encode (message : OrderReplaceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.originalOrderReferenceNumber
    ++ (encodeUInt 8 message.newOrderReferenceNumber
    ++ (encodeUInt 4 message.shares
    ++ (encodeUInt 4 message.price
    ++ (Display.encode message.display)))))

def decode (bytes : List UInt8) : Option (OrderReplaceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (originalOrderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (newOrderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (display, bytes) ← Display.decode bytes
  pure ({ nanoseconds, originalOrderReferenceNumber, newOrderReferenceNumber, shares, price, display }, bytes)

@[simp] theorem encode_length (message : OrderReplaceMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Display.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Display.decode_encode, some_bind]
  rfl

end OrderReplaceMessage

/-- Order Display Message: 12 bytes -/
structure OrderDisplayMessage where
  nanoseconds : BitVec 32
  orderReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDisplayMessage

def encode (message : OrderDisplayMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderReferenceNumber)

def decode (bytes : List UInt8) : Option (OrderDisplayMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, orderReferenceNumber }, bytes)

@[simp] theorem encode_length (message : OrderDisplayMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderDisplayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDisplayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDisplayMessage

/-- Trade Message: 35 bytes -/
structure TradeMessage where
  nanoseconds : BitVec 32
  orderReferenceNumber : BitVec 64
  side : Side
  shares : BitVec 32
  stock : Alpha 6
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
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, orderReferenceNumber, side, shares, stock, price, matchNumber }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 35 := by
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

/-- Cross Trade Message: 31 bytes -/
structure CrossTradeMessage where
  nanoseconds : BitVec 32
  crossShares : BitVec 64
  stock : Alpha 6
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
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (crossPrice, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  pure ({ nanoseconds, crossShares, stock, crossPrice, matchNumber, crossType }, bytes)

@[simp] theorem encode_length (message : CrossTradeMessage) : (encode message).length = 31 := by
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

/-- Net Order Imbalance Indicator Message: 41 bytes -/
structure NetOrderImbalanceIndicatorMessage where
  nanoseconds : BitVec 32
  pairedShares : BitVec 64
  imbalanceShares : BitVec 64
  imbalanceDirection : ImbalanceDirection
  stock : Alpha 6
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
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (farPrice, bytes) ← decodeUInt 4 bytes
  let (nearPrice, bytes) ← decodeUInt 4 bytes
  let (currentReferencePrice, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (priceVariationIndicator, bytes) ← PriceVariationIndicator.decode bytes
  pure ({ nanoseconds, pairedShares, imbalanceShares, imbalanceDirection, stock, farPrice, nearPrice, currentReferencePrice, crossType, priceVariationIndicator }, bytes)

@[simp] theorem encode_length (message : NetOrderImbalanceIndicatorMessage) : (encode message).length = 41 := by
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

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | timestampMessage (message : TimestampMessage) -- "T" 0x54
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | stockDirectoryMessage (message : StockDirectoryMessage) -- "R" 0x52
  | stockTradingActionMessage (message : StockTradingActionMessage) -- "H" 0x48
  | marketParticipantPositionMessage (message : MarketParticipantPositionMessage) -- "L" 0x4C
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | addOrderWithMpidMessage (message : AddOrderWithMpidMessage) -- "F" 0x46
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- "C" 0x43
  | orderCancelMessage (message : OrderCancelMessage) -- "X" 0x58
  | orderDeleteMessage (message : OrderDeleteMessage) -- "D" 0x44
  | orderReplaceMessage (message : OrderReplaceMessage) -- "U" 0x55
  | orderDisplayMessage (message : OrderDisplayMessage) -- "V" 0x56
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | crossTradeMessage (message : CrossTradeMessage) -- "Q" 0x51
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  | netOrderImbalanceIndicatorMessage (message : NetOrderImbalanceIndicatorMessage) -- "I" 0x49
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .timestampMessage _ => 84
  | .systemEventMessage _ => 83
  | .stockDirectoryMessage _ => 82
  | .stockTradingActionMessage _ => 72
  | .marketParticipantPositionMessage _ => 76
  | .addOrderMessage _ => 65
  | .addOrderWithMpidMessage _ => 70
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .orderCancelMessage _ => 88
  | .orderDeleteMessage _ => 68
  | .orderReplaceMessage _ => 85
  | .orderDisplayMessage _ => 86
  | .tradeMessage _ => 80
  | .crossTradeMessage _ => 81
  | .brokenTradeMessage _ => 66
  | .netOrderImbalanceIndicatorMessage _ => 73

def encode : Payload → List UInt8
  | .timestampMessage message => TimestampMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .stockDirectoryMessage message => StockDirectoryMessage.encode message
  | .stockTradingActionMessage message => StockTradingActionMessage.encode message
  | .marketParticipantPositionMessage message => MarketParticipantPositionMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .addOrderWithMpidMessage message => AddOrderWithMpidMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderReplaceMessage message => OrderReplaceMessage.encode message
  | .orderDisplayMessage message => OrderDisplayMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .crossTradeMessage message => CrossTradeMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .netOrderImbalanceIndicatorMessage message => NetOrderImbalanceIndicatorMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 41 := by
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
  | orderDisplayMessage inner =>
    simp only [encode, OrderDisplayMessage.encode_length]
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

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (TimestampMessage.decode bytes).map fun (message, rest) => (.timestampMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (StockDirectoryMessage.decode bytes).map fun (message, rest) => (.stockDirectoryMessage message, rest)
  else if tag = 72 then (StockTradingActionMessage.decode bytes).map fun (message, rest) => (.stockTradingActionMessage message, rest)
  else if tag = 76 then (MarketParticipantPositionMessage.decode bytes).map fun (message, rest) => (.marketParticipantPositionMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 70 then (AddOrderWithMpidMessage.decode bytes).map fun (message, rest) => (.addOrderWithMpidMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 88 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 85 then (OrderReplaceMessage.decode bytes).map fun (message, rest) => (.orderReplaceMessage message, rest)
  else if tag = 86 then (OrderDisplayMessage.decode bytes).map fun (message, rest) => (.orderDisplayMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 81 then (CrossTradeMessage.decode bytes).map fun (message, rest) => (.crossTradeMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 73 then (NetOrderImbalanceIndicatorMessage.decode bytes).map fun (message, rest) => (.netOrderImbalanceIndicatorMessage message, rest)
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
  | timestampMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TimestampMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockDirectoryMessage.encode_length]
    omega
  | stockTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockTradingActionMessage.encode_length]
    omega
  | marketParticipantPositionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketParticipantPositionMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | addOrderWithMpidMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderWithMpidMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancelMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderReplaceMessage.encode_length]
    omega
  | orderDisplayMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDisplayMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | crossTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CrossTradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | netOrderImbalanceIndicatorMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NetOrderImbalanceIndicatorMessage.encode_length]
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

end Omi.NasdaqNsmequitiesTotalviewItchV40F
