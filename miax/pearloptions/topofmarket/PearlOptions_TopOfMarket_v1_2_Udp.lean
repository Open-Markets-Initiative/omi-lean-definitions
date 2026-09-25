import Omi.Wire

/-!
# Miami International Holdings Top of Market v1.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Application Message is not framed: its length Packet Length is not an integer it reads.

Note: Udp Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxPearloptionsTopofmarketMachV12Udp

/-- Call Or Put: one byte code -/
def CallOrPut.codes : List UInt8 :=
  [0x43, 0x50]

inductive CallOrPut where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ CallOrPut.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CallOrPut

def toByte : CallOrPut → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CallOrPut :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : CallOrPut :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CallOrPut) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CallOrPut) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CallOrPut × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CallOrPut) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CallOrPut) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CallOrPut

/-- Restricted Option: one byte code -/
def RestrictedOption.codes : List UInt8 :=
  [0x59, 0x4E]

inductive RestrictedOption where
  | acceptPositionClosing -- Accept Position Closing
  | acceptOpenAndClose -- Accept Open And Close
  | unlisted (byte : { byte : UInt8 // byte ∉ RestrictedOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RestrictedOption

def toByte : RestrictedOption → UInt8
  | .acceptPositionClosing => 0x59
  | .acceptOpenAndClose => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RestrictedOption :=
  if byte = 0x59 then .acceptPositionClosing
  else .acceptOpenAndClose

def ofByte (byte : UInt8) : RestrictedOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RestrictedOption) : ofByte value.toByte = value := by
  cases value with
  | acceptPositionClosing => decide
  | acceptOpenAndClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RestrictedOption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RestrictedOption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RestrictedOption) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RestrictedOption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RestrictedOption

/-- Long Term Option: one byte code -/
def LongTermOption.codes : List UInt8 :=
  [0x59, 0x4E]

inductive LongTermOption where
  | farMonthExpiration -- Far Month Expiration
  | nearMonthExpiration -- Near Month Expiration
  | unlisted (byte : { byte : UInt8 // byte ∉ LongTermOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LongTermOption

def toByte : LongTermOption → UInt8
  | .farMonthExpiration => 0x59
  | .nearMonthExpiration => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LongTermOption :=
  if byte = 0x59 then .farMonthExpiration
  else .nearMonthExpiration

def ofByte (byte : UInt8) : LongTermOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LongTermOption) : ofByte value.toByte = value := by
  cases value with
  | farMonthExpiration => decide
  | nearMonthExpiration => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LongTermOption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LongTermOption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LongTermOption) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LongTermOption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LongTermOption

/-- Active On Pearl: one byte code -/
def ActiveOnPearl.codes : List UInt8 :=
  [0x41, 0x49]

inductive ActiveOnPearl where
  | active -- Active
  | inactive -- Inactive
  | unlisted (byte : { byte : UInt8 // byte ∉ ActiveOnPearl.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ActiveOnPearl

def toByte : ActiveOnPearl → UInt8
  | .active => 0x41
  | .inactive => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ActiveOnPearl :=
  if byte = 0x41 then .active
  else .inactive

def ofByte (byte : UInt8) : ActiveOnPearl :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ActiveOnPearl) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | inactive => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ActiveOnPearl) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ActiveOnPearl × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ActiveOnPearl) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ActiveOnPearl) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ActiveOnPearl

/-- Pearl Bbo Posting Increment Indicator: one byte code -/
def PearlBboPostingIncrementIndicator.codes : List UInt8 :=
  [0x50, 0x4E, 0x44]

inductive PearlBboPostingIncrementIndicator where
  | penny -- Penny
  | pennyOrNickel -- Penny Or Nickel
  | nickelOrDime -- Nickel Or Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ PearlBboPostingIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PearlBboPostingIncrementIndicator

def toByte : PearlBboPostingIncrementIndicator → UInt8
  | .penny => 0x50
  | .pennyOrNickel => 0x4E
  | .nickelOrDime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PearlBboPostingIncrementIndicator :=
  if byte = 0x50 then .penny
  else if byte = 0x4E then .pennyOrNickel
  else .nickelOrDime

def ofByte (byte : UInt8) : PearlBboPostingIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PearlBboPostingIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny => decide
  | pennyOrNickel => decide
  | nickelOrDime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PearlBboPostingIncrementIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PearlBboPostingIncrementIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PearlBboPostingIncrementIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PearlBboPostingIncrementIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PearlBboPostingIncrementIndicator

/-- Liquidity Acceptance Increment Indicator: one byte code -/
def LiquidityAcceptanceIncrementIndicator.codes : List UInt8 :=
  [0x50, 0x4E, 0x44]

inductive LiquidityAcceptanceIncrementIndicator where
  | penny -- Penny
  | pennyOrNickel -- Penny Or Nickel
  | nickelOrDime -- Nickel Or Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityAcceptanceIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityAcceptanceIncrementIndicator

def toByte : LiquidityAcceptanceIncrementIndicator → UInt8
  | .penny => 0x50
  | .pennyOrNickel => 0x4E
  | .nickelOrDime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityAcceptanceIncrementIndicator :=
  if byte = 0x50 then .penny
  else if byte = 0x4E then .pennyOrNickel
  else .nickelOrDime

def ofByte (byte : UInt8) : LiquidityAcceptanceIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityAcceptanceIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny => decide
  | pennyOrNickel => decide
  | nickelOrDime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityAcceptanceIncrementIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityAcceptanceIncrementIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityAcceptanceIncrementIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LiquidityAcceptanceIncrementIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityAcceptanceIncrementIndicator

/-- Opening Underlying Market Code: one byte code -/
def OpeningUnderlyingMarketCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive OpeningUnderlyingMarketCode where
  | nyseAmex -- Nyse Amex
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nse -- Nse
  | finraAdf -- Finra Adf
  | marketIndependent -- Market Independent
  | miaxPearlEquities -- Miax Pearl Equities
  | ise -- Ise
  | edga -- Edga
  | edgx -- Edgx
  | ltse -- Ltse
  | cse -- Cse
  | nyseEuronext -- Nyse Euronext
  | nyseArca -- Nyse Arca
  | nasdaqOmxUtp -- Nasdaq Omx Utp
  | nasdaqOmxCta -- Nasdaq Omx Cta
  | memx -- Memx
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqOmxPhlx -- Nasdaq Omx Phlx
  | batsY -- Bats Y
  | bats -- Bats
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningUnderlyingMarketCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningUnderlyingMarketCode

def toByte : OpeningUnderlyingMarketCode → UInt8
  | .nyseAmex => 0x41
  | .nasdaqOmxBx => 0x42
  | .nse => 0x43
  | .finraAdf => 0x44
  | .marketIndependent => 0x45
  | .miaxPearlEquities => 0x48
  | .ise => 0x49
  | .edga => 0x4A
  | .edgx => 0x4B
  | .ltse => 0x4C
  | .cse => 0x4D
  | .nyseEuronext => 0x4E
  | .nyseArca => 0x50
  | .nasdaqOmxUtp => 0x51
  | .nasdaqOmxCta => 0x54
  | .memx => 0x55
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqOmxPhlx => 0x58
  | .batsY => 0x59
  | .bats => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningUnderlyingMarketCode :=
  if byte = 0x41 then .nyseAmex
  else if byte = 0x42 then .nasdaqOmxBx
  else if byte = 0x43 then .nse
  else if byte = 0x44 then .finraAdf
  else if byte = 0x45 then .marketIndependent
  else if byte = 0x48 then .miaxPearlEquities
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .edga
  else if byte = 0x4B then .edgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .cse
  else if byte = 0x4E then .nyseEuronext
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaqOmxUtp
  else if byte = 0x54 then .nasdaqOmxCta
  else if byte = 0x55 then .memx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqOmxPhlx
  else if byte = 0x59 then .batsY
  else .bats

def ofByte (byte : UInt8) : OpeningUnderlyingMarketCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningUnderlyingMarketCode) : ofByte value.toByte = value := by
  cases value with
  | nyseAmex => decide
  | nasdaqOmxBx => decide
  | nse => decide
  | finraAdf => decide
  | marketIndependent => decide
  | miaxPearlEquities => decide
  | ise => decide
  | edga => decide
  | edgx => decide
  | ltse => decide
  | cse => decide
  | nyseEuronext => decide
  | nyseArca => decide
  | nasdaqOmxUtp => decide
  | nasdaqOmxCta => decide
  | memx => decide
  | iex => decide
  | cbsx => decide
  | nasdaqOmxPhlx => decide
  | batsY => decide
  | bats => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpeningUnderlyingMarketCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpeningUnderlyingMarketCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpeningUnderlyingMarketCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpeningUnderlyingMarketCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpeningUnderlyingMarketCode

/-- System Status: one byte code -/
def SystemStatus.codes : List UInt8 :=
  [0x53, 0x43, 0x31, 0x32]

inductive SystemStatus where
  | startOfSystemHours -- Start Of System Hours
  | endOfSystemHours -- End Of System Hours
  | startTestSession -- Start Test Session
  | endOfTestSession -- End Of Test Session
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemStatus

def toByte : SystemStatus → UInt8
  | .startOfSystemHours => 0x53
  | .endOfSystemHours => 0x43
  | .startTestSession => 0x31
  | .endOfTestSession => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemStatus :=
  if byte = 0x53 then .startOfSystemHours
  else if byte = 0x43 then .endOfSystemHours
  else if byte = 0x31 then .startTestSession
  else .endOfTestSession

def ofByte (byte : UInt8) : SystemStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemStatus) : ofByte value.toByte = value := by
  cases value with
  | startOfSystemHours => decide
  | endOfSystemHours => decide
  | startTestSession => decide
  | endOfTestSession => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SystemStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SystemStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SystemStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SystemStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SystemStatus

/-- Pbbo Condition: one byte code -/
def PbboCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x52, 0x54]

inductive PbboCondition where
  | regular -- Regular
  | publicCustomerInterest -- Public Customer Interest
  | notFirm -- Not Firm
  | reserved -- Reserved
  | tradingHalt -- Trading Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ PbboCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PbboCondition

def toByte : PbboCondition → UInt8
  | .regular => 0x41
  | .publicCustomerInterest => 0x42
  | .notFirm => 0x43
  | .reserved => 0x52
  | .tradingHalt => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PbboCondition :=
  if byte = 0x41 then .regular
  else if byte = 0x42 then .publicCustomerInterest
  else if byte = 0x43 then .notFirm
  else if byte = 0x52 then .reserved
  else .tradingHalt

def ofByte (byte : UInt8) : PbboCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PbboCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | publicCustomerInterest => decide
  | notFirm => decide
  | reserved => decide
  | tradingHalt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PbboCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PbboCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PbboCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PbboCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PbboCondition

/-- Bid Condition: one byte code -/
def BidCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x52, 0x54]

inductive BidCondition where
  | regular -- Regular
  | publicCustomerInterest -- Public Customer Interest
  | notFirm -- Not Firm
  | reserved -- Reserved
  | tradingHalt -- Trading Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ BidCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BidCondition

def toByte : BidCondition → UInt8
  | .regular => 0x41
  | .publicCustomerInterest => 0x42
  | .notFirm => 0x43
  | .reserved => 0x52
  | .tradingHalt => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BidCondition :=
  if byte = 0x41 then .regular
  else if byte = 0x42 then .publicCustomerInterest
  else if byte = 0x43 then .notFirm
  else if byte = 0x52 then .reserved
  else .tradingHalt

def ofByte (byte : UInt8) : BidCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BidCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | publicCustomerInterest => decide
  | notFirm => decide
  | reserved => decide
  | tradingHalt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BidCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BidCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BidCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BidCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BidCondition

/-- Offer Condition: one byte code -/
def OfferCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x52, 0x54]

inductive OfferCondition where
  | regular -- Regular
  | publicCustomerInterest -- Public Customer Interest
  | notFirm -- Not Firm
  | reserved -- Reserved
  | tradingHalt -- Trading Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ OfferCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OfferCondition

def toByte : OfferCondition → UInt8
  | .regular => 0x41
  | .publicCustomerInterest => 0x42
  | .notFirm => 0x43
  | .reserved => 0x52
  | .tradingHalt => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OfferCondition :=
  if byte = 0x41 then .regular
  else if byte = 0x42 then .publicCustomerInterest
  else if byte = 0x43 then .notFirm
  else if byte = 0x52 then .reserved
  else .tradingHalt

def ofByte (byte : UInt8) : OfferCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OfferCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | publicCustomerInterest => decide
  | notFirm => decide
  | reserved => decide
  | tradingHalt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OfferCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OfferCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OfferCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OfferCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OfferCondition

/-- Trade Condition: one byte code -/
def TradeCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x58, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73, 0x74]

inductive TradeCondition where
  | regular -- Regular
  | cancelOfTradePreviouslyReportedOtherThanAsTheLastOrOpening -- Cancel Of Trade Previously Reported Other Than As The Last Or Opening
  | lateAndIsOutOfSequence -- Late And Is Out Of Sequence
  | cancelOfTheLastReportedTrade -- Cancel Of The Last Reported Trade
  | lateAndIsInCorrectSequence -- Late And Is In Correct Sequence
  | cancelOfTheFirstReportedTrade -- Cancel Of The First Reported Trade
  | lateReportOfTheOpeningTradeAndIsOutOfSequence -- Late Report Of The Opening Trade And Is Out Of Sequence
  | cancelOfTheOnlyReportedTrade -- Cancel Of The Only Reported Trade
  | lateReportOfTheOpeningTradeAndIsInCorrectSequence -- Late Report Of The Opening Trade And Is In Correct Sequence
  | auto -- Auto
  | reopeningOfAnOption -- Reopening Of An Option
  | reserved -- Reserved
  | reserved_4c -- Reserved
  | reserved_4d -- Reserved
  | reserved_4e -- Reserved
  | reserved_4f -- Reserved
  | reserved_50 -- Reserved
  | reserved_51 -- Reserved
  | executionOfAnOrderWhichWasStoppedAtAPriceThatDidNotConstituteATradeThroughOnAnotherMarketAtTheTimeOfTheStop -- Execution Of An Order Which Was Stopped At A Price That Did Not Constitute A Trade Through On Another Market At The Time Of The Stop
  | executionOfAnIsoOrder -- Execution Of An Iso Order
  | reserved_54 -- Reserved
  | tradeThroughExempt -- Trade Through Exempt
  | pairedPrime -- Paired Prime
  | reserved_62 -- Reserved
  | primeCustomerToCustomerCrossOrPrimeQcc -- Prime Customer To Customer Cross Or Prime Qcc
  | reserved_64 -- Reserved
  | reserved_65 -- Reserved
  | complexTransactionThatIsNotComplexStocktiedAndDoesNotInvolveLegging -- Complex Transaction That Is Not Complex Stocktied And Does Not Involve Legging
  | complexPrimeTransactionThatIsNotComplexStocktiedAndDoesNotInvolveLegging -- Complex Prime Transaction That Is Not Complex Stocktied And Does Not Involve Legging
  | complexPrimeCustomerToCustomerCrossOrComplexPrimeQccTransactionThatIsNotComplexStocktied -- Complex Prime Customer To Customer Cross Or Complex Prime Qcc Transaction That Is Not Complex Stocktied
  | reserved_69 -- Reserved
  | complexLeggingTransactionThatIsNotComplexStocktied -- Complex Legging Transaction That Is Not Complex Stocktied
  | complexPrimeStocktiedTransactionThatDoesNotInvolveLegging -- Complex Prime Stocktied Transaction That Does Not Involve Legging
  | complexPrimeLeggingTransactionThatIsNotComplexStocktied -- Complex Prime Legging Transaction That Is Not Complex Stocktied
  | reserved_6d -- Reserved
  | complexStocktiedTransactionThatDoesNotInvolveLegging -- Complex Stocktied Transaction That Does Not Involve Legging
  | complexCustomerToCustomerCrossStocktiedOrComplexQccStocktiedTransaction -- Complex Customer To Customer Cross Stocktied Or Complex Qcc Stocktied Transaction
  | reserved_70 -- Reserved
  | reserved_71 -- Reserved
  | reserved_72 -- Reserved
  | reserved_73 -- Reserved
  | reserved_74 -- Reserved
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCondition

def toByte : TradeCondition → UInt8
  | .regular => 0x20
  | .cancelOfTradePreviouslyReportedOtherThanAsTheLastOrOpening => 0x41
  | .lateAndIsOutOfSequence => 0x42
  | .cancelOfTheLastReportedTrade => 0x43
  | .lateAndIsInCorrectSequence => 0x44
  | .cancelOfTheFirstReportedTrade => 0x45
  | .lateReportOfTheOpeningTradeAndIsOutOfSequence => 0x46
  | .cancelOfTheOnlyReportedTrade => 0x47
  | .lateReportOfTheOpeningTradeAndIsInCorrectSequence => 0x48
  | .auto => 0x49
  | .reopeningOfAnOption => 0x4A
  | .reserved => 0x4B
  | .reserved_4c => 0x4C
  | .reserved_4d => 0x4D
  | .reserved_4e => 0x4E
  | .reserved_4f => 0x4F
  | .reserved_50 => 0x50
  | .reserved_51 => 0x51
  | .executionOfAnOrderWhichWasStoppedAtAPriceThatDidNotConstituteATradeThroughOnAnotherMarketAtTheTimeOfTheStop => 0x52
  | .executionOfAnIsoOrder => 0x53
  | .reserved_54 => 0x54
  | .tradeThroughExempt => 0x58
  | .pairedPrime => 0x61
  | .reserved_62 => 0x62
  | .primeCustomerToCustomerCrossOrPrimeQcc => 0x63
  | .reserved_64 => 0x64
  | .reserved_65 => 0x65
  | .complexTransactionThatIsNotComplexStocktiedAndDoesNotInvolveLegging => 0x66
  | .complexPrimeTransactionThatIsNotComplexStocktiedAndDoesNotInvolveLegging => 0x67
  | .complexPrimeCustomerToCustomerCrossOrComplexPrimeQccTransactionThatIsNotComplexStocktied => 0x68
  | .reserved_69 => 0x69
  | .complexLeggingTransactionThatIsNotComplexStocktied => 0x6A
  | .complexPrimeStocktiedTransactionThatDoesNotInvolveLegging => 0x6B
  | .complexPrimeLeggingTransactionThatIsNotComplexStocktied => 0x6C
  | .reserved_6d => 0x6D
  | .complexStocktiedTransactionThatDoesNotInvolveLegging => 0x6E
  | .complexCustomerToCustomerCrossStocktiedOrComplexQccStocktiedTransaction => 0x6F
  | .reserved_70 => 0x70
  | .reserved_71 => 0x71
  | .reserved_72 => 0x72
  | .reserved_73 => 0x73
  | .reserved_74 => 0x74
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCondition :=
  if byte = 0x20 then .regular
  else if byte = 0x41 then .cancelOfTradePreviouslyReportedOtherThanAsTheLastOrOpening
  else if byte = 0x42 then .lateAndIsOutOfSequence
  else if byte = 0x43 then .cancelOfTheLastReportedTrade
  else if byte = 0x44 then .lateAndIsInCorrectSequence
  else if byte = 0x45 then .cancelOfTheFirstReportedTrade
  else if byte = 0x46 then .lateReportOfTheOpeningTradeAndIsOutOfSequence
  else if byte = 0x47 then .cancelOfTheOnlyReportedTrade
  else if byte = 0x48 then .lateReportOfTheOpeningTradeAndIsInCorrectSequence
  else if byte = 0x49 then .auto
  else if byte = 0x4A then .reopeningOfAnOption
  else if byte = 0x4B then .reserved
  else if byte = 0x4C then .reserved_4c
  else if byte = 0x4D then .reserved_4d
  else if byte = 0x4E then .reserved_4e
  else if byte = 0x4F then .reserved_4f
  else if byte = 0x50 then .reserved_50
  else if byte = 0x51 then .reserved_51
  else if byte = 0x52 then .executionOfAnOrderWhichWasStoppedAtAPriceThatDidNotConstituteATradeThroughOnAnotherMarketAtTheTimeOfTheStop
  else if byte = 0x53 then .executionOfAnIsoOrder
  else if byte = 0x54 then .reserved_54
  else if byte = 0x58 then .tradeThroughExempt
  else if byte = 0x61 then .pairedPrime
  else if byte = 0x62 then .reserved_62
  else if byte = 0x63 then .primeCustomerToCustomerCrossOrPrimeQcc
  else if byte = 0x64 then .reserved_64
  else if byte = 0x65 then .reserved_65
  else if byte = 0x66 then .complexTransactionThatIsNotComplexStocktiedAndDoesNotInvolveLegging
  else if byte = 0x67 then .complexPrimeTransactionThatIsNotComplexStocktiedAndDoesNotInvolveLegging
  else if byte = 0x68 then .complexPrimeCustomerToCustomerCrossOrComplexPrimeQccTransactionThatIsNotComplexStocktied
  else if byte = 0x69 then .reserved_69
  else if byte = 0x6A then .complexLeggingTransactionThatIsNotComplexStocktied
  else if byte = 0x6B then .complexPrimeStocktiedTransactionThatDoesNotInvolveLegging
  else if byte = 0x6C then .complexPrimeLeggingTransactionThatIsNotComplexStocktied
  else if byte = 0x6D then .reserved_6d
  else if byte = 0x6E then .complexStocktiedTransactionThatDoesNotInvolveLegging
  else if byte = 0x6F then .complexCustomerToCustomerCrossStocktiedOrComplexQccStocktiedTransaction
  else if byte = 0x70 then .reserved_70
  else if byte = 0x71 then .reserved_71
  else if byte = 0x72 then .reserved_72
  else if byte = 0x73 then .reserved_73
  else .reserved_74

def ofByte (byte : UInt8) : TradeCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | cancelOfTradePreviouslyReportedOtherThanAsTheLastOrOpening => decide
  | lateAndIsOutOfSequence => decide
  | cancelOfTheLastReportedTrade => decide
  | lateAndIsInCorrectSequence => decide
  | cancelOfTheFirstReportedTrade => decide
  | lateReportOfTheOpeningTradeAndIsOutOfSequence => decide
  | cancelOfTheOnlyReportedTrade => decide
  | lateReportOfTheOpeningTradeAndIsInCorrectSequence => decide
  | auto => decide
  | reopeningOfAnOption => decide
  | reserved => decide
  | reserved_4c => decide
  | reserved_4d => decide
  | reserved_4e => decide
  | reserved_4f => decide
  | reserved_50 => decide
  | reserved_51 => decide
  | executionOfAnOrderWhichWasStoppedAtAPriceThatDidNotConstituteATradeThroughOnAnotherMarketAtTheTimeOfTheStop => decide
  | executionOfAnIsoOrder => decide
  | reserved_54 => decide
  | tradeThroughExempt => decide
  | pairedPrime => decide
  | reserved_62 => decide
  | primeCustomerToCustomerCrossOrPrimeQcc => decide
  | reserved_64 => decide
  | reserved_65 => decide
  | complexTransactionThatIsNotComplexStocktiedAndDoesNotInvolveLegging => decide
  | complexPrimeTransactionThatIsNotComplexStocktiedAndDoesNotInvolveLegging => decide
  | complexPrimeCustomerToCustomerCrossOrComplexPrimeQccTransactionThatIsNotComplexStocktied => decide
  | reserved_69 => decide
  | complexLeggingTransactionThatIsNotComplexStocktied => decide
  | complexPrimeStocktiedTransactionThatDoesNotInvolveLegging => decide
  | complexPrimeLeggingTransactionThatIsNotComplexStocktied => decide
  | reserved_6d => decide
  | complexStocktiedTransactionThatDoesNotInvolveLegging => decide
  | complexCustomerToCustomerCrossStocktiedOrComplexQccStocktiedTransaction => decide
  | reserved_70 => decide
  | reserved_71 => decide
  | reserved_72 => decide
  | reserved_73 => decide
  | reserved_74 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCondition

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x48, 0x52, 0x4F]

inductive TradingStatus where
  | halted -- Halted
  | resumed -- Resumed
  | opened -- Opened
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .halted => 0x48
  | .resumed => 0x52
  | .opened => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x48 then .halted
  else if byte = 0x52 then .resumed
  else .opened

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | resumed => decide
  | opened => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingStatus

/-- Event Reason: one byte code -/
def EventReason.codes : List UInt8 :=
  [0x41, 0x4D]

inductive EventReason where
  | automatic -- Automatic
  | manual -- Manual
  | unlisted (byte : { byte : UInt8 // byte ∉ EventReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventReason

def toByte : EventReason → UInt8
  | .automatic => 0x41
  | .manual => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventReason :=
  if byte = 0x41 then .automatic
  else .manual

def ofByte (byte : UInt8) : EventReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventReason) : ofByte value.toByte = value := by
  cases value with
  | automatic => decide
  | manual => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventReason

/-- Heartbeat: 0 bytes -/
structure Heartbeat where
  deriving DecidableEq, Repr

namespace Heartbeat

def encode (_ : Heartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (Heartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : Heartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : Heartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end Heartbeat

/-- Start Of Session: 0 bytes -/
structure StartOfSession where
  deriving DecidableEq, Repr

namespace StartOfSession

def encode (_ : StartOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (StartOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : StartOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : StartOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end StartOfSession

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

/-- System Time Message: 4 bytes -/
structure SystemTimeMessage where
  seconds : BitVec 32
  deriving DecidableEq, Repr

namespace SystemTimeMessage

def encode (message : SystemTimeMessage) : List UInt8 :=
  encodeUIntLE 4 message.seconds

def decode (bytes : List UInt8) : Option (SystemTimeMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ seconds }, bytes)

@[simp] theorem encode_length (message : SystemTimeMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SystemTimeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemTimeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SystemTimeMessage

/-- Series Update Message: 72 bytes -/
structure SeriesUpdateMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  underlyingSymbol : Alpha 11
  securitySymbol : Alpha 6
  expirationDate : Alpha 8
  strikePrice : BitVec 32
  callOrPut : CallOrPut
  openingTime : Alpha 8
  closingTime : Alpha 8
  restrictedOption : RestrictedOption
  longTermOption : LongTermOption
  activeOnPearl : ActiveOnPearl
  pearlBboPostingIncrementIndicator : PearlBboPostingIncrementIndicator
  liquidityAcceptanceIncrementIndicator : LiquidityAcceptanceIncrementIndicator
  openingUnderlyingMarketCode : OpeningUnderlyingMarketCode
  reserved12 : Alpha 12
  deriving DecidableEq, Repr

namespace SeriesUpdateMessage

def encode (message : SeriesUpdateMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.expirationDate
    ++ (encodeUIntLE 4 message.strikePrice
    ++ (CallOrPut.encode message.callOrPut
    ++ (Alpha.encode message.openingTime
    ++ (Alpha.encode message.closingTime
    ++ (RestrictedOption.encode message.restrictedOption
    ++ (LongTermOption.encode message.longTermOption
    ++ (ActiveOnPearl.encode message.activeOnPearl
    ++ (PearlBboPostingIncrementIndicator.encode message.pearlBboPostingIncrementIndicator
    ++ (LiquidityAcceptanceIncrementIndicator.encode message.liquidityAcceptanceIncrementIndicator
    ++ (OpeningUnderlyingMarketCode.encode message.openingUnderlyingMarketCode
    ++ (Alpha.encode message.reserved12)))))))))))))))

def decode (bytes : List UInt8) : Option (SeriesUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (securitySymbol, bytes) ← Alpha.decode 6 bytes
  let (expirationDate, bytes) ← Alpha.decode 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 4 bytes
  let (callOrPut, bytes) ← CallOrPut.decode bytes
  let (openingTime, bytes) ← Alpha.decode 8 bytes
  let (closingTime, bytes) ← Alpha.decode 8 bytes
  let (restrictedOption, bytes) ← RestrictedOption.decode bytes
  let (longTermOption, bytes) ← LongTermOption.decode bytes
  let (activeOnPearl, bytes) ← ActiveOnPearl.decode bytes
  let (pearlBboPostingIncrementIndicator, bytes) ← PearlBboPostingIncrementIndicator.decode bytes
  let (liquidityAcceptanceIncrementIndicator, bytes) ← LiquidityAcceptanceIncrementIndicator.decode bytes
  let (openingUnderlyingMarketCode, bytes) ← OpeningUnderlyingMarketCode.decode bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  pure ({ nanoseconds, productId, underlyingSymbol, securitySymbol, expirationDate, strikePrice, callOrPut, openingTime, closingTime, restrictedOption, longTermOption, activeOnPearl, pearlBboPostingIncrementIndicator, liquidityAcceptanceIncrementIndicator, openingUnderlyingMarketCode, reserved12 }, bytes)

@[simp] theorem encode_length (message : SeriesUpdateMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CallOrPut.encode_length, RestrictedOption.encode_length, LongTermOption.encode_length, ActiveOnPearl.encode_length, PearlBboPostingIncrementIndicator.encode_length, LiquidityAcceptanceIncrementIndicator.encode_length, OpeningUnderlyingMarketCode.encode_length]

theorem encode_length_pos (message : SeriesUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CallOrPut.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RestrictedOption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongTermOption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ActiveOnPearl.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PearlBboPostingIncrementIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityAcceptanceIncrementIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningUnderlyingMarketCode.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SeriesUpdateMessage

/-- System State Message: 17 bytes -/
structure SystemStateMessage where
  nanoseconds : BitVec 32
  toMVersion : Alpha 8
  sessionId : BitVec 32
  systemStatus : SystemStatus
  deriving DecidableEq, Repr

namespace SystemStateMessage

def encode (message : SystemStateMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.toMVersion
    ++ (encodeUIntLE 4 message.sessionId
    ++ (SystemStatus.encode message.systemStatus)))

def decode (bytes : List UInt8) : Option (SystemStateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (toMVersion, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  pure ({ nanoseconds, toMVersion, sessionId, systemStatus }, bytes)

@[simp] theorem encode_length (message : SystemStateMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SystemStatus.encode_length]

theorem encode_length_pos (message : SystemStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [SystemStatus.decode_encode, some_bind]
  rfl

end SystemStateMessage

/-- Top Of Market Best Bid Or Offer Compact Format Bid Message: 15 bytes -/
structure TopOfMarketBestBidOrOfferCompactFormatBidMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  pbboPriceShort : BitVec 16
  pbboSizeShort : BitVec 16
  pbboPriorityCustomerSizeShort : BitVec 16
  pbboCondition : PbboCondition
  deriving DecidableEq, Repr

namespace TopOfMarketBestBidOrOfferCompactFormatBidMessage

def encode (message : TopOfMarketBestBidOrOfferCompactFormatBidMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.pbboPriceShort
    ++ (encodeUIntLE 2 message.pbboSizeShort
    ++ (encodeUIntLE 2 message.pbboPriorityCustomerSizeShort
    ++ (PbboCondition.encode message.pbboCondition)))))

def decode (bytes : List UInt8) : Option (TopOfMarketBestBidOrOfferCompactFormatBidMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (pbboPriceShort, bytes) ← decodeUIntLE 2 bytes
  let (pbboSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (pbboPriorityCustomerSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (pbboCondition, bytes) ← PbboCondition.decode bytes
  pure ({ nanoseconds, productId, pbboPriceShort, pbboSizeShort, pbboPriorityCustomerSizeShort, pbboCondition }, bytes)

@[simp] theorem encode_length (message : TopOfMarketBestBidOrOfferCompactFormatBidMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PbboCondition.encode_length]

theorem encode_length_pos (message : TopOfMarketBestBidOrOfferCompactFormatBidMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfMarketBestBidOrOfferCompactFormatBidMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [PbboCondition.decode_encode, some_bind]
  rfl

end TopOfMarketBestBidOrOfferCompactFormatBidMessage

/-- Top Of Market Best Bid Or Offer Compact Format Bid Priority Customer Message: 15 bytes -/
structure TopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  pbboPriceShort : BitVec 16
  pbboSizeShort : BitVec 16
  pbboPriorityCustomerSizeShort : BitVec 16
  pbboCondition : PbboCondition
  deriving DecidableEq, Repr

namespace TopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage

def encode (message : TopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.pbboPriceShort
    ++ (encodeUIntLE 2 message.pbboSizeShort
    ++ (encodeUIntLE 2 message.pbboPriorityCustomerSizeShort
    ++ (PbboCondition.encode message.pbboCondition)))))

def decode (bytes : List UInt8) : Option (TopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (pbboPriceShort, bytes) ← decodeUIntLE 2 bytes
  let (pbboSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (pbboPriorityCustomerSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (pbboCondition, bytes) ← PbboCondition.decode bytes
  pure ({ nanoseconds, productId, pbboPriceShort, pbboSizeShort, pbboPriorityCustomerSizeShort, pbboCondition }, bytes)

@[simp] theorem encode_length (message : TopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PbboCondition.encode_length]

theorem encode_length_pos (message : TopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [PbboCondition.decode_encode, some_bind]
  rfl

end TopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage

/-- Top Of Market Best Bid Or Offer Compact Format Offer Message: 15 bytes -/
structure TopOfMarketBestBidOrOfferCompactFormatOfferMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  pbboPriceShort : BitVec 16
  pbboSizeShort : BitVec 16
  pbboPriorityCustomerSizeShort : BitVec 16
  pbboCondition : PbboCondition
  deriving DecidableEq, Repr

namespace TopOfMarketBestBidOrOfferCompactFormatOfferMessage

def encode (message : TopOfMarketBestBidOrOfferCompactFormatOfferMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.pbboPriceShort
    ++ (encodeUIntLE 2 message.pbboSizeShort
    ++ (encodeUIntLE 2 message.pbboPriorityCustomerSizeShort
    ++ (PbboCondition.encode message.pbboCondition)))))

def decode (bytes : List UInt8) : Option (TopOfMarketBestBidOrOfferCompactFormatOfferMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (pbboPriceShort, bytes) ← decodeUIntLE 2 bytes
  let (pbboSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (pbboPriorityCustomerSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (pbboCondition, bytes) ← PbboCondition.decode bytes
  pure ({ nanoseconds, productId, pbboPriceShort, pbboSizeShort, pbboPriorityCustomerSizeShort, pbboCondition }, bytes)

@[simp] theorem encode_length (message : TopOfMarketBestBidOrOfferCompactFormatOfferMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PbboCondition.encode_length]

theorem encode_length_pos (message : TopOfMarketBestBidOrOfferCompactFormatOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfMarketBestBidOrOfferCompactFormatOfferMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [PbboCondition.decode_encode, some_bind]
  rfl

end TopOfMarketBestBidOrOfferCompactFormatOfferMessage

/-- Top Of Market Best Bid Or Offer Compact Format Offer Priority Customer Message: 15 bytes -/
structure TopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  pbboPriceShort : BitVec 16
  pbboSizeShort : BitVec 16
  pbboPriorityCustomerSizeShort : BitVec 16
  pbboCondition : PbboCondition
  deriving DecidableEq, Repr

namespace TopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage

def encode (message : TopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.pbboPriceShort
    ++ (encodeUIntLE 2 message.pbboSizeShort
    ++ (encodeUIntLE 2 message.pbboPriorityCustomerSizeShort
    ++ (PbboCondition.encode message.pbboCondition)))))

def decode (bytes : List UInt8) : Option (TopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (pbboPriceShort, bytes) ← decodeUIntLE 2 bytes
  let (pbboSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (pbboPriorityCustomerSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (pbboCondition, bytes) ← PbboCondition.decode bytes
  pure ({ nanoseconds, productId, pbboPriceShort, pbboSizeShort, pbboPriorityCustomerSizeShort, pbboCondition }, bytes)

@[simp] theorem encode_length (message : TopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PbboCondition.encode_length]

theorem encode_length_pos (message : TopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [PbboCondition.decode_encode, some_bind]
  rfl

end TopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage

/-- Top Of Market Best Bid Or Offer Wide Format Bid Message: 21 bytes -/
structure TopOfMarketBestBidOrOfferWideFormatBidMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  pbboPriceLong : BitVec 32
  pbboSizeLong : BitVec 32
  pbboPriorityCustomerSizeLong : BitVec 32
  pbboCondition : PbboCondition
  deriving DecidableEq, Repr

namespace TopOfMarketBestBidOrOfferWideFormatBidMessage

def encode (message : TopOfMarketBestBidOrOfferWideFormatBidMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.pbboPriceLong
    ++ (encodeUIntLE 4 message.pbboSizeLong
    ++ (encodeUIntLE 4 message.pbboPriorityCustomerSizeLong
    ++ (PbboCondition.encode message.pbboCondition)))))

def decode (bytes : List UInt8) : Option (TopOfMarketBestBidOrOfferWideFormatBidMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (pbboPriceLong, bytes) ← decodeUIntLE 4 bytes
  let (pbboSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (pbboPriorityCustomerSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (pbboCondition, bytes) ← PbboCondition.decode bytes
  pure ({ nanoseconds, productId, pbboPriceLong, pbboSizeLong, pbboPriorityCustomerSizeLong, pbboCondition }, bytes)

@[simp] theorem encode_length (message : TopOfMarketBestBidOrOfferWideFormatBidMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PbboCondition.encode_length]

theorem encode_length_pos (message : TopOfMarketBestBidOrOfferWideFormatBidMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfMarketBestBidOrOfferWideFormatBidMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [PbboCondition.decode_encode, some_bind]
  rfl

end TopOfMarketBestBidOrOfferWideFormatBidMessage

/-- Top Of Market Best Bid Or Offer Wide Format Bid Priority Customer Message: 21 bytes -/
structure TopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  pbboPriceLong : BitVec 32
  pbboSizeLong : BitVec 32
  pbboPriorityCustomerSizeLong : BitVec 32
  pbboCondition : PbboCondition
  deriving DecidableEq, Repr

namespace TopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage

def encode (message : TopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.pbboPriceLong
    ++ (encodeUIntLE 4 message.pbboSizeLong
    ++ (encodeUIntLE 4 message.pbboPriorityCustomerSizeLong
    ++ (PbboCondition.encode message.pbboCondition)))))

def decode (bytes : List UInt8) : Option (TopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (pbboPriceLong, bytes) ← decodeUIntLE 4 bytes
  let (pbboSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (pbboPriorityCustomerSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (pbboCondition, bytes) ← PbboCondition.decode bytes
  pure ({ nanoseconds, productId, pbboPriceLong, pbboSizeLong, pbboPriorityCustomerSizeLong, pbboCondition }, bytes)

@[simp] theorem encode_length (message : TopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PbboCondition.encode_length]

theorem encode_length_pos (message : TopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [PbboCondition.decode_encode, some_bind]
  rfl

end TopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage

/-- Top Of Market Best Bid Or Offer Wide Format Offer Message: 21 bytes -/
structure TopOfMarketBestBidOrOfferWideFormatOfferMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  pbboPriceLong : BitVec 32
  pbboSizeLong : BitVec 32
  pbboPriorityCustomerSizeLong : BitVec 32
  pbboCondition : PbboCondition
  deriving DecidableEq, Repr

namespace TopOfMarketBestBidOrOfferWideFormatOfferMessage

def encode (message : TopOfMarketBestBidOrOfferWideFormatOfferMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.pbboPriceLong
    ++ (encodeUIntLE 4 message.pbboSizeLong
    ++ (encodeUIntLE 4 message.pbboPriorityCustomerSizeLong
    ++ (PbboCondition.encode message.pbboCondition)))))

def decode (bytes : List UInt8) : Option (TopOfMarketBestBidOrOfferWideFormatOfferMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (pbboPriceLong, bytes) ← decodeUIntLE 4 bytes
  let (pbboSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (pbboPriorityCustomerSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (pbboCondition, bytes) ← PbboCondition.decode bytes
  pure ({ nanoseconds, productId, pbboPriceLong, pbboSizeLong, pbboPriorityCustomerSizeLong, pbboCondition }, bytes)

@[simp] theorem encode_length (message : TopOfMarketBestBidOrOfferWideFormatOfferMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PbboCondition.encode_length]

theorem encode_length_pos (message : TopOfMarketBestBidOrOfferWideFormatOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfMarketBestBidOrOfferWideFormatOfferMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [PbboCondition.decode_encode, some_bind]
  rfl

end TopOfMarketBestBidOrOfferWideFormatOfferMessage

/-- Top Of Market Best Bid Or Offer Wide Format Offer Priority Customer Message: 21 bytes -/
structure TopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  pbboPriceLong : BitVec 32
  pbboSizeLong : BitVec 32
  pbboPriorityCustomerSizeLong : BitVec 32
  pbboCondition : PbboCondition
  deriving DecidableEq, Repr

namespace TopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage

def encode (message : TopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.pbboPriceLong
    ++ (encodeUIntLE 4 message.pbboSizeLong
    ++ (encodeUIntLE 4 message.pbboPriorityCustomerSizeLong
    ++ (PbboCondition.encode message.pbboCondition)))))

def decode (bytes : List UInt8) : Option (TopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (pbboPriceLong, bytes) ← decodeUIntLE 4 bytes
  let (pbboSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (pbboPriorityCustomerSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (pbboCondition, bytes) ← PbboCondition.decode bytes
  pure ({ nanoseconds, productId, pbboPriceLong, pbboSizeLong, pbboPriorityCustomerSizeLong, pbboCondition }, bytes)

@[simp] theorem encode_length (message : TopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PbboCondition.encode_length]

theorem encode_length_pos (message : TopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [PbboCondition.decode_encode, some_bind]
  rfl

end TopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage

/-- Double Sided Top Of Market Best Bid Or Offer Compact Format Message: 22 bytes -/
structure DoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  bidPriorityCustomerSizeShort : BitVec 16
  bidCondition : BidCondition
  offerPriceShort : BitVec 16
  offerSizeShort : BitVec 16
  offerPriorityCustomerSizeShort : BitVec 16
  offerCondition : OfferCondition
  deriving DecidableEq, Repr

namespace DoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage

def encode (message : DoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.bidPriceShort
    ++ (encodeUIntLE 2 message.bidSizeShort
    ++ (encodeUIntLE 2 message.bidPriorityCustomerSizeShort
    ++ (BidCondition.encode message.bidCondition
    ++ (encodeUIntLE 2 message.offerPriceShort
    ++ (encodeUIntLE 2 message.offerSizeShort
    ++ (encodeUIntLE 2 message.offerPriorityCustomerSizeShort
    ++ (OfferCondition.encode message.offerCondition)))))))))

def decode (bytes : List UInt8) : Option (DoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (bidPriceShort, bytes) ← decodeUIntLE 2 bytes
  let (bidSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (bidPriorityCustomerSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (bidCondition, bytes) ← BidCondition.decode bytes
  let (offerPriceShort, bytes) ← decodeUIntLE 2 bytes
  let (offerSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (offerPriorityCustomerSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (offerCondition, bytes) ← OfferCondition.decode bytes
  pure ({ nanoseconds, productId, bidPriceShort, bidSizeShort, bidPriorityCustomerSizeShort, bidCondition, offerPriceShort, offerSizeShort, offerPriorityCustomerSizeShort, offerCondition }, bytes)

@[simp] theorem encode_length (message : DoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, BidCondition.encode_length, OfferCondition.encode_length]

theorem encode_length_pos (message : DoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BidCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [OfferCondition.decode_encode, some_bind]
  rfl

end DoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage

/-- Double Sided Top Of Market Best Bid Or Offer Wide Format Message: 34 bytes -/
structure DoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  bidPriceLong : BitVec 32
  bidSizeLong : BitVec 32
  bidPriorityCustomerSizeLong : BitVec 32
  bidCondition : BidCondition
  offerPriceLong : BitVec 32
  offerSizeLong : BitVec 32
  offerPriorityCustomerSizeLong : BitVec 32
  offerCondition : OfferCondition
  deriving DecidableEq, Repr

namespace DoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage

def encode (message : DoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.bidPriceLong
    ++ (encodeUIntLE 4 message.bidSizeLong
    ++ (encodeUIntLE 4 message.bidPriorityCustomerSizeLong
    ++ (BidCondition.encode message.bidCondition
    ++ (encodeUIntLE 4 message.offerPriceLong
    ++ (encodeUIntLE 4 message.offerSizeLong
    ++ (encodeUIntLE 4 message.offerPriorityCustomerSizeLong
    ++ (OfferCondition.encode message.offerCondition)))))))))

def decode (bytes : List UInt8) : Option (DoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (bidPriceLong, bytes) ← decodeUIntLE 4 bytes
  let (bidSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (bidPriorityCustomerSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (bidCondition, bytes) ← BidCondition.decode bytes
  let (offerPriceLong, bytes) ← decodeUIntLE 4 bytes
  let (offerSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (offerPriorityCustomerSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (offerCondition, bytes) ← OfferCondition.decode bytes
  pure ({ nanoseconds, productId, bidPriceLong, bidSizeLong, bidPriorityCustomerSizeLong, bidCondition, offerPriceLong, offerSizeLong, offerPriorityCustomerSizeLong, offerCondition }, bytes)

@[simp] theorem encode_length (message : DoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, BidCondition.encode_length, OfferCondition.encode_length]

theorem encode_length_pos (message : DoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BidCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [OfferCondition.decode_encode, some_bind]
  rfl

end DoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage

/-- Last Sale Message: 27 bytes -/
structure LastSaleMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  tradeId : BitVec 32
  correctionNumber : BitVec 8
  referenceTradeId : BitVec 32
  referenceCorrectionNumber : BitVec 8
  tradePrice : BitVec 32
  tradeSize : BitVec 32
  tradeCondition : TradeCondition
  deriving DecidableEq, Repr

namespace LastSaleMessage

def encode (message : LastSaleMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 1 message.correctionNumber
    ++ (encodeUIntLE 4 message.referenceTradeId
    ++ (encodeUIntLE 1 message.referenceCorrectionNumber
    ++ (encodeUIntLE 4 message.tradePrice
    ++ (encodeUIntLE 4 message.tradeSize
    ++ (TradeCondition.encode message.tradeCondition))))))))

def decode (bytes : List UInt8) : Option (LastSaleMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (correctionNumber, bytes) ← decodeUIntLE 1 bytes
  let (referenceTradeId, bytes) ← decodeUIntLE 4 bytes
  let (referenceCorrectionNumber, bytes) ← decodeUIntLE 1 bytes
  let (tradePrice, bytes) ← decodeUIntLE 4 bytes
  let (tradeSize, bytes) ← decodeUIntLE 4 bytes
  let (tradeCondition, bytes) ← TradeCondition.decode bytes
  pure ({ nanoseconds, productId, tradeId, correctionNumber, referenceTradeId, referenceCorrectionNumber, tradePrice, tradeSize, tradeCondition }, bytes)

@[simp] theorem encode_length (message : LastSaleMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCondition.encode_length]

theorem encode_length_pos (message : LastSaleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LastSaleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [TradeCondition.decode_encode, some_bind]
  rfl

end LastSaleMessage

/-- Trade Cancel Message: 22 bytes -/
structure TradeCancelMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  tradeId : BitVec 32
  correctionNumber : BitVec 8
  tradePrice : BitVec 32
  tradeSize : BitVec 32
  tradeCondition : TradeCondition
  deriving DecidableEq, Repr

namespace TradeCancelMessage

def encode (message : TradeCancelMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 1 message.correctionNumber
    ++ (encodeUIntLE 4 message.tradePrice
    ++ (encodeUIntLE 4 message.tradeSize
    ++ (TradeCondition.encode message.tradeCondition))))))

def decode (bytes : List UInt8) : Option (TradeCancelMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (correctionNumber, bytes) ← decodeUIntLE 1 bytes
  let (tradePrice, bytes) ← decodeUIntLE 4 bytes
  let (tradeSize, bytes) ← decodeUIntLE 4 bytes
  let (tradeCondition, bytes) ← TradeCondition.decode bytes
  pure ({ nanoseconds, productId, tradeId, correctionNumber, tradePrice, tradeSize, tradeCondition }, bytes)

@[simp] theorem encode_length (message : TradeCancelMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCondition.encode_length]

theorem encode_length_pos (message : TradeCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [TradeCondition.decode_encode, some_bind]
  rfl

end TradeCancelMessage

/-- Underlying Trading Status Notification Message: 25 bytes -/
structure UnderlyingTradingStatusNotificationMessage where
  nanoseconds : BitVec 32
  underlyingSymbol : Alpha 11
  tradingStatus : TradingStatus
  eventReason : EventReason
  expectedEventTimeSecondsPart : BitVec 32
  expectedEventTimeNanoSecondsPart : BitVec 32
  deriving DecidableEq, Repr

namespace UnderlyingTradingStatusNotificationMessage

def encode (message : UnderlyingTradingStatusNotificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.underlyingSymbol
    ++ (TradingStatus.encode message.tradingStatus
    ++ (EventReason.encode message.eventReason
    ++ (encodeUIntLE 4 message.expectedEventTimeSecondsPart
    ++ (encodeUIntLE 4 message.expectedEventTimeNanoSecondsPart)))))

def decode (bytes : List UInt8) : Option (UnderlyingTradingStatusNotificationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (eventReason, bytes) ← EventReason.decode bytes
  let (expectedEventTimeSecondsPart, bytes) ← decodeUIntLE 4 bytes
  let (expectedEventTimeNanoSecondsPart, bytes) ← decodeUIntLE 4 bytes
  pure ({ nanoseconds, underlyingSymbol, tradingStatus, eventReason, expectedEventTimeSecondsPart, expectedEventTimeNanoSecondsPart }, bytes)

@[simp] theorem encode_length (message : UnderlyingTradingStatusNotificationMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradingStatus.encode_length, EventReason.encode_length]

theorem encode_length_pos (message : UnderlyingTradingStatusNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingTradingStatusNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end UnderlyingTradingStatusNotificationMessage

/-- Any Data, selected by Message Type -/
inductive Data where
  | systemTimeMessage (message : SystemTimeMessage) -- "1" 0x31
  | seriesUpdateMessage (message : SeriesUpdateMessage) -- "P" 0x50
  | systemStateMessage (message : SystemStateMessage) -- "S" 0x53
  | topOfMarketBestBidOrOfferCompactFormatBidMessage (message : TopOfMarketBestBidOrOfferCompactFormatBidMessage) -- "B" 0x42
  | topOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage (message : TopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage) -- "h" 0x68
  | topOfMarketBestBidOrOfferCompactFormatOfferMessage (message : TopOfMarketBestBidOrOfferCompactFormatOfferMessage) -- "O" 0x4F
  | topOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage (message : TopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage) -- "i" 0x69
  | topOfMarketBestBidOrOfferWideFormatBidMessage (message : TopOfMarketBestBidOrOfferWideFormatBidMessage) -- "W" 0x57
  | topOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage (message : TopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage) -- "j" 0x6A
  | topOfMarketBestBidOrOfferWideFormatOfferMessage (message : TopOfMarketBestBidOrOfferWideFormatOfferMessage) -- "A" 0x41
  | topOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage (message : TopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage) -- "k" 0x6B
  | doubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage (message : DoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage) -- "d" 0x64
  | doubleSidedTopOfMarketBestBidOrOfferWideFormatMessage (message : DoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage) -- "D" 0x44
  | lastSaleMessage (message : LastSaleMessage) -- "T" 0x54
  | tradeCancelMessage (message : TradeCancelMessage) -- "X" 0x58
  | underlyingTradingStatusNotificationMessage (message : UnderlyingTradingStatusNotificationMessage) -- "H" 0x48
  deriving DecidableEq, Repr

namespace Data

/-- The Message Type each message is sent under -/
def tag : Data → BitVec 8
  | .systemTimeMessage _ => 49
  | .seriesUpdateMessage _ => 80
  | .systemStateMessage _ => 83
  | .topOfMarketBestBidOrOfferCompactFormatBidMessage _ => 66
  | .topOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage _ => 104
  | .topOfMarketBestBidOrOfferCompactFormatOfferMessage _ => 79
  | .topOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage _ => 105
  | .topOfMarketBestBidOrOfferWideFormatBidMessage _ => 87
  | .topOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage _ => 106
  | .topOfMarketBestBidOrOfferWideFormatOfferMessage _ => 65
  | .topOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage _ => 107
  | .doubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage _ => 100
  | .doubleSidedTopOfMarketBestBidOrOfferWideFormatMessage _ => 68
  | .lastSaleMessage _ => 84
  | .tradeCancelMessage _ => 88
  | .underlyingTradingStatusNotificationMessage _ => 72

def encode : Data → List UInt8
  | .systemTimeMessage message => SystemTimeMessage.encode message
  | .seriesUpdateMessage message => SeriesUpdateMessage.encode message
  | .systemStateMessage message => SystemStateMessage.encode message
  | .topOfMarketBestBidOrOfferCompactFormatBidMessage message => TopOfMarketBestBidOrOfferCompactFormatBidMessage.encode message
  | .topOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage message => TopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage.encode message
  | .topOfMarketBestBidOrOfferCompactFormatOfferMessage message => TopOfMarketBestBidOrOfferCompactFormatOfferMessage.encode message
  | .topOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage message => TopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage.encode message
  | .topOfMarketBestBidOrOfferWideFormatBidMessage message => TopOfMarketBestBidOrOfferWideFormatBidMessage.encode message
  | .topOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage message => TopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage.encode message
  | .topOfMarketBestBidOrOfferWideFormatOfferMessage message => TopOfMarketBestBidOrOfferWideFormatOfferMessage.encode message
  | .topOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage message => TopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage.encode message
  | .doubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage message => DoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage.encode message
  | .doubleSidedTopOfMarketBestBidOrOfferWideFormatMessage message => DoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage.encode message
  | .lastSaleMessage message => LastSaleMessage.encode message
  | .tradeCancelMessage message => TradeCancelMessage.encode message
  | .underlyingTradingStatusNotificationMessage message => UnderlyingTradingStatusNotificationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Data) : (encode message).length ≤ 72 := by
  cases message with
  | systemTimeMessage inner =>
    simp only [encode, SystemTimeMessage.encode_length]
    omega
  | seriesUpdateMessage inner =>
    simp only [encode, SeriesUpdateMessage.encode_length]
    omega
  | systemStateMessage inner =>
    simp only [encode, SystemStateMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferCompactFormatBidMessage inner =>
    simp only [encode, TopOfMarketBestBidOrOfferCompactFormatBidMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage inner =>
    simp only [encode, TopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferCompactFormatOfferMessage inner =>
    simp only [encode, TopOfMarketBestBidOrOfferCompactFormatOfferMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage inner =>
    simp only [encode, TopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferWideFormatBidMessage inner =>
    simp only [encode, TopOfMarketBestBidOrOfferWideFormatBidMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage inner =>
    simp only [encode, TopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferWideFormatOfferMessage inner =>
    simp only [encode, TopOfMarketBestBidOrOfferWideFormatOfferMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage inner =>
    simp only [encode, TopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage.encode_length]
    omega
  | doubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage inner =>
    simp only [encode, DoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage.encode_length]
    omega
  | doubleSidedTopOfMarketBestBidOrOfferWideFormatMessage inner =>
    simp only [encode, DoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage.encode_length]
    omega
  | lastSaleMessage inner =>
    simp only [encode, LastSaleMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [encode, TradeCancelMessage.encode_length]
    omega
  | underlyingTradingStatusNotificationMessage inner =>
    simp only [encode, UnderlyingTradingStatusNotificationMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Data × List UInt8) :=
  if tag = 49 then (SystemTimeMessage.decode bytes).map fun (message, rest) => (.systemTimeMessage message, rest)
  else if tag = 80 then (SeriesUpdateMessage.decode bytes).map fun (message, rest) => (.seriesUpdateMessage message, rest)
  else if tag = 83 then (SystemStateMessage.decode bytes).map fun (message, rest) => (.systemStateMessage message, rest)
  else if tag = 66 then (TopOfMarketBestBidOrOfferCompactFormatBidMessage.decode bytes).map fun (message, rest) => (.topOfMarketBestBidOrOfferCompactFormatBidMessage message, rest)
  else if tag = 104 then (TopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage.decode bytes).map fun (message, rest) => (.topOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage message, rest)
  else if tag = 79 then (TopOfMarketBestBidOrOfferCompactFormatOfferMessage.decode bytes).map fun (message, rest) => (.topOfMarketBestBidOrOfferCompactFormatOfferMessage message, rest)
  else if tag = 105 then (TopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage.decode bytes).map fun (message, rest) => (.topOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage message, rest)
  else if tag = 87 then (TopOfMarketBestBidOrOfferWideFormatBidMessage.decode bytes).map fun (message, rest) => (.topOfMarketBestBidOrOfferWideFormatBidMessage message, rest)
  else if tag = 106 then (TopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage.decode bytes).map fun (message, rest) => (.topOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage message, rest)
  else if tag = 65 then (TopOfMarketBestBidOrOfferWideFormatOfferMessage.decode bytes).map fun (message, rest) => (.topOfMarketBestBidOrOfferWideFormatOfferMessage message, rest)
  else if tag = 107 then (TopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage.decode bytes).map fun (message, rest) => (.topOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage message, rest)
  else if tag = 100 then (DoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage.decode bytes).map fun (message, rest) => (.doubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage message, rest)
  else if tag = 68 then (DoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage.decode bytes).map fun (message, rest) => (.doubleSidedTopOfMarketBestBidOrOfferWideFormatMessage message, rest)
  else if tag = 84 then (LastSaleMessage.decode bytes).map fun (message, rest) => (.lastSaleMessage message, rest)
  else if tag = 88 then (TradeCancelMessage.decode bytes).map fun (message, rest) => (.tradeCancelMessage message, rest)
  else if tag = 72 then (UnderlyingTradingStatusNotificationMessage.decode bytes).map fun (message, rest) => (.underlyingTradingStatusNotificationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Data) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Data

/-- Application Message -/
structure ApplicationMessage where
  data : Data
  deriving DecidableEq, Repr

namespace ApplicationMessage

def encode (message : ApplicationMessage) : List UInt8 :=
  encodeUInt 1 (Data.tag message.data)
    ++ (Data.encode message.data)

def decode (bytes : List UInt8) : Option (ApplicationMessage × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (data, bytes) ← Data.decode messageType bytes
  pure ({ data }, bytes)

theorem encode_length_pos (message : ApplicationMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ApplicationMessage) : (encode message).length ≤ 73 := by
  unfold encode
  cases message.data with
  | systemTimeMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SystemTimeMessage.encode_length]
    omega
  | seriesUpdateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SeriesUpdateMessage.encode_length]
    omega
  | systemStateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SystemStateMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferCompactFormatBidMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TopOfMarketBestBidOrOfferCompactFormatBidMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferCompactFormatOfferMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TopOfMarketBestBidOrOfferCompactFormatOfferMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferWideFormatBidMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TopOfMarketBestBidOrOfferWideFormatBidMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferWideFormatOfferMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TopOfMarketBestBidOrOfferWideFormatOfferMessage.encode_length]
    omega
  | topOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage.encode_length]
    omega
  | doubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, DoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage.encode_length]
    omega
  | doubleSidedTopOfMarketBestBidOrOfferWideFormatMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, DoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage.encode_length]
    omega
  | lastSaleMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, LastSaleMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TradeCancelMessage.encode_length]
    omega
  | underlyingTradingStatusNotificationMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, UnderlyingTradingStatusNotificationMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ApplicationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Data.decode_encode, some_bind]
  rfl

end ApplicationMessage

/-- Any Payload, selected by Packet Type -/
inductive Payload where
  | heartbeat (message : Heartbeat) -- 0
  | startOfSession (message : StartOfSession) -- 1
  | endOfSession (message : EndOfSession) -- 2
  | applicationMessage (message : ApplicationMessage) -- 3
  deriving DecidableEq, Repr

namespace Payload

/-- The Packet Type each message is sent under -/
def tag : Payload → BitVec 8
  | .heartbeat _ => 0
  | .startOfSession _ => 1
  | .endOfSession _ => 2
  | .applicationMessage _ => 3

def encode : Payload → List UInt8
  | .heartbeat message => Heartbeat.encode message
  | .startOfSession message => StartOfSession.encode message
  | .endOfSession message => EndOfSession.encode message
  | .applicationMessage message => ApplicationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 73 := by
  cases message with
  | heartbeat inner =>
    simp only [encode, Heartbeat.encode_length]
    omega
  | startOfSession inner =>
    simp only [encode, StartOfSession.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 0 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 1 then (StartOfSession.decode bytes).map fun (message, rest) => (.startOfSession message, rest)
  else if tag = 2 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
  else if tag = 3 then (ApplicationMessage.decode bytes).map fun (message, rest) => (.applicationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Mach Message -/
structure MachMessage where
  sequenceNumber : BitVec 64
  sessionNumber : BitVec 8
  payload : Payload
  deriving DecidableEq, Repr

namespace MachMessage

def encodeBody (message : MachMessage) : List UInt8 :=
  encodeUIntLE 1 (Payload.tag message.payload)
    ++ (encodeUIntLE 1 message.sessionNumber
    ++ (Payload.encode message.payload))

def decodeBody (sequenceNumber : BitVec 64) (bytes : List UInt8) : Option (MachMessage × List UInt8) := do
  let (packetType, bytes) ← decodeUIntLE 1 bytes
  let (sessionNumber, bytes) ← decodeUIntLE 1 bytes
  let (payload, bytes) ← Payload.decode packetType bytes
  pure ({ sequenceNumber, sessionNumber, payload }, bytes)

theorem decodeBody_encodeBody (message : MachMessage) (rest : List UInt8) :
    decodeBody message.sequenceNumber (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : MachMessage) : (encodeBody message).length + 10 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | heartbeat inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Heartbeat.encode_length]
    omega
  | startOfSession inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, StartOfSession.encode_length]
    omega
  | endOfSession inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EndOfSession.encode_length]
    omega
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega

/-- Size rule: Packet Length counts the bytes after it plus 10, so it is written from the body and checked on decode; Sequence Number is read ahead of it -/
def encode (message : MachMessage) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeFramedLE 2 10 encodeBody message)

def decode (bytes : List UInt8) : Option (MachMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  decodeFramedLE 2 10 (decodeBody sequenceNumber) bytes

@[simp] theorem decode_encode (message : MachMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  exact decodeFramedLE_encodeFramedLE 2 10 encodeBody (decodeBody message.sequenceNumber) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : MachMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, encodeFramedLE_length]
  omega

end MachMessage

/-- Udp Packet -/
structure UdpPacket where
  machMessage : List MachMessage
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  encodeMany MachMessage.encode message.machMessage

def decode (bytes : List UInt8) : Option UdpPacket := do
  let machMessage ← decodeAll MachMessage.decode bytes.length bytes
  pure { machMessage }

theorem decode_encode (message : UdpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany MachMessage.encode MachMessage.decode MachMessage.decode_encode MachMessage.encode_length_pos message.machMessage _ (encodeMany_length_ge MachMessage.encode MachMessage.encode_length_pos message.machMessage), some_bind]
  rfl

end UdpPacket

end Omi.MiaxPearloptionsTopofmarketMachV12Udp
