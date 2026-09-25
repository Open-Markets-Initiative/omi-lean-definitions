import Omi.Wire

/-!
# Miami International Holdings Top Of Market v2.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Application Message is not framed: its length Packet Length is not an integer it reads.

Note: Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxPearloptionsTopofmarketMachV22

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

/-- Active On Miax: one byte code -/
def ActiveOnMiax.codes : List UInt8 :=
  [0x41, 0x49]

inductive ActiveOnMiax where
  | active -- Active
  | inactive -- Inactive
  | unlisted (byte : { byte : UInt8 // byte ∉ ActiveOnMiax.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ActiveOnMiax

def toByte : ActiveOnMiax → UInt8
  | .active => 0x41
  | .inactive => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ActiveOnMiax :=
  if byte = 0x41 then .active
  else .inactive

def ofByte (byte : UInt8) : ActiveOnMiax :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ActiveOnMiax) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | inactive => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ActiveOnMiax) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ActiveOnMiax × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ActiveOnMiax) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ActiveOnMiax) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ActiveOnMiax

/-- Miax Bbo Posting Increment Indicator: one byte code -/
def MiaxBboPostingIncrementIndicator.codes : List UInt8 :=
  [0x50, 0x4E, 0x44]

inductive MiaxBboPostingIncrementIndicator where
  | penny -- Penny
  | pennyOrNickel -- Penny Or Nickel
  | nickelOrDime -- Nickel Or Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ MiaxBboPostingIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MiaxBboPostingIncrementIndicator

def toByte : MiaxBboPostingIncrementIndicator → UInt8
  | .penny => 0x50
  | .pennyOrNickel => 0x4E
  | .nickelOrDime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MiaxBboPostingIncrementIndicator :=
  if byte = 0x50 then .penny
  else if byte = 0x4E then .pennyOrNickel
  else .nickelOrDime

def ofByte (byte : UInt8) : MiaxBboPostingIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MiaxBboPostingIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny => decide
  | pennyOrNickel => decide
  | nickelOrDime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MiaxBboPostingIncrementIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MiaxBboPostingIncrementIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MiaxBboPostingIncrementIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MiaxBboPostingIncrementIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MiaxBboPostingIncrementIndicator

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
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x49, 0x4A, 0x4B, 0x4D, 0x4E, 0x50, 0x51, 0x54, 0x56, 0x58, 0x59, 0x5A]

inductive OpeningUnderlyingMarketCode where
  | nyseAmex -- Nyse Amex
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nse -- Nse
  | finraAdf -- Finra Adf
  | marketIndependent -- Market Independent
  | ise -- Ise
  | edga -- Edga
  | edgx -- Edgx
  | cse -- Cse
  | nyseEuronext -- Nyse Euronext
  | nyseArca -- Nyse Arca
  | nasdaqOmxUtp -- Nasdaq Omx Utp
  | nasdaqOmxCta -- Nasdaq Omx Cta
  | iex -- Iex
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
  | .ise => 0x49
  | .edga => 0x4A
  | .edgx => 0x4B
  | .cse => 0x4D
  | .nyseEuronext => 0x4E
  | .nyseArca => 0x50
  | .nasdaqOmxUtp => 0x51
  | .nasdaqOmxCta => 0x54
  | .iex => 0x56
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
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .edga
  else if byte = 0x4B then .edgx
  else if byte = 0x4D then .cse
  else if byte = 0x4E then .nyseEuronext
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaqOmxUtp
  else if byte = 0x54 then .nasdaqOmxCta
  else if byte = 0x56 then .iex
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
  | ise => decide
  | edga => decide
  | edgx => decide
  | cse => decide
  | nyseEuronext => decide
  | nyseArca => decide
  | nasdaqOmxUtp => decide
  | nasdaqOmxCta => decide
  | iex => decide
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

/-- Mbbo Condition: one byte code -/
def MbboCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x52, 0x54]

inductive MbboCondition where
  | regular -- Regular
  | publicCustomerInterest -- Public Customer Interest
  | notFirm -- Not Firm
  | reserved -- Reserved
  | tradingHalt -- Trading Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ MbboCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MbboCondition

def toByte : MbboCondition → UInt8
  | .regular => 0x41
  | .publicCustomerInterest => 0x42
  | .notFirm => 0x43
  | .reserved => 0x52
  | .tradingHalt => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MbboCondition :=
  if byte = 0x41 then .regular
  else if byte = 0x42 then .publicCustomerInterest
  else if byte = 0x43 then .notFirm
  else if byte = 0x52 then .reserved
  else .tradingHalt

def ofByte (byte : UInt8) : MbboCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MbboCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | publicCustomerInterest => decide
  | notFirm => decide
  | reserved => decide
  | tradingHalt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MbboCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MbboCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MbboCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MbboCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MbboCondition

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
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x58]

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
  | reserved -- Reserved
  | reopeningOfAnOption -- Reopening Of An Option
  | reserved_4b -- Reserved
  | aBuyAndASellInTheSameClass -- A Buy And A Sell In The Same Class
  | aBuyAndASellInAPutAndACall -- A Buy And A Sell In A Put And A Call
  | reserved_4e -- Reserved
  | reserved_4f -- Reserved
  | buyOrSellOfACallOrPut -- Buy Or Sell Of A Call Or Put
  | buyOfACallAndASellOfAPutForTheSameUnderlyingStockOrIndex -- Buy Of A Call And A Sell Of A Put For The Same Underlying Stock Or Index
  | executionOfAnOrderWhichWasStoppedAtAPriceThatDidNotConstituteATradeThroughOnAnotherMarketAtTheTimeOfTheStop -- Execution Of An Order Which Was Stopped At A Price That Did Not Constitute A Trade Through On Another Market At The Time Of The Stop
  | executionOfAnIsoOrder -- Execution Of An Iso Order
  | reserved_54 -- Reserved
  | tradeThroughExempt -- Trade Through Exempt
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
  | .reserved => 0x49
  | .reopeningOfAnOption => 0x4A
  | .reserved_4b => 0x4B
  | .aBuyAndASellInTheSameClass => 0x4C
  | .aBuyAndASellInAPutAndACall => 0x4D
  | .reserved_4e => 0x4E
  | .reserved_4f => 0x4F
  | .buyOrSellOfACallOrPut => 0x50
  | .buyOfACallAndASellOfAPutForTheSameUnderlyingStockOrIndex => 0x51
  | .executionOfAnOrderWhichWasStoppedAtAPriceThatDidNotConstituteATradeThroughOnAnotherMarketAtTheTimeOfTheStop => 0x52
  | .executionOfAnIsoOrder => 0x53
  | .reserved_54 => 0x54
  | .tradeThroughExempt => 0x58
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
  else if byte = 0x49 then .reserved
  else if byte = 0x4A then .reopeningOfAnOption
  else if byte = 0x4B then .reserved_4b
  else if byte = 0x4C then .aBuyAndASellInTheSameClass
  else if byte = 0x4D then .aBuyAndASellInAPutAndACall
  else if byte = 0x4E then .reserved_4e
  else if byte = 0x4F then .reserved_4f
  else if byte = 0x50 then .buyOrSellOfACallOrPut
  else if byte = 0x51 then .buyOfACallAndASellOfAPutForTheSameUnderlyingStockOrIndex
  else if byte = 0x52 then .executionOfAnOrderWhichWasStoppedAtAPriceThatDidNotConstituteATradeThroughOnAnotherMarketAtTheTimeOfTheStop
  else if byte = 0x53 then .executionOfAnIsoOrder
  else if byte = 0x54 then .reserved_54
  else .tradeThroughExempt

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
  | reserved => decide
  | reopeningOfAnOption => decide
  | reserved_4b => decide
  | aBuyAndASellInTheSameClass => decide
  | aBuyAndASellInAPutAndACall => decide
  | reserved_4e => decide
  | reserved_4f => decide
  | buyOrSellOfACallOrPut => decide
  | buyOfACallAndASellOfAPutForTheSameUnderlyingStockOrIndex => decide
  | executionOfAnOrderWhichWasStoppedAtAPriceThatDidNotConstituteATradeThroughOnAnotherMarketAtTheTimeOfTheStop => decide
  | executionOfAnIsoOrder => decide
  | reserved_54 => decide
  | tradeThroughExempt => decide
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

/-- Simple Series Update Message: 72 bytes -/
structure SimpleSeriesUpdateMessage where
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
  activeOnMiax : ActiveOnMiax
  miaxBboPostingIncrementIndicator : MiaxBboPostingIncrementIndicator
  liquidityAcceptanceIncrementIndicator : LiquidityAcceptanceIncrementIndicator
  openingUnderlyingMarketCode : OpeningUnderlyingMarketCode
  priorityQuoteWidth : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace SimpleSeriesUpdateMessage

def encode (message : SimpleSeriesUpdateMessage) : List UInt8 :=
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
    ++ (ActiveOnMiax.encode message.activeOnMiax
    ++ (MiaxBboPostingIncrementIndicator.encode message.miaxBboPostingIncrementIndicator
    ++ (LiquidityAcceptanceIncrementIndicator.encode message.liquidityAcceptanceIncrementIndicator
    ++ (OpeningUnderlyingMarketCode.encode message.openingUnderlyingMarketCode
    ++ (encodeUIntLE 4 message.priorityQuoteWidth
    ++ (Alpha.encode message.reserved8))))))))))))))))

def decode (bytes : List UInt8) : Option (SimpleSeriesUpdateMessage × List UInt8) := do
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
  let (activeOnMiax, bytes) ← ActiveOnMiax.decode bytes
  let (miaxBboPostingIncrementIndicator, bytes) ← MiaxBboPostingIncrementIndicator.decode bytes
  let (liquidityAcceptanceIncrementIndicator, bytes) ← LiquidityAcceptanceIncrementIndicator.decode bytes
  let (openingUnderlyingMarketCode, bytes) ← OpeningUnderlyingMarketCode.decode bytes
  let (priorityQuoteWidth, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ nanoseconds, productId, underlyingSymbol, securitySymbol, expirationDate, strikePrice, callOrPut, openingTime, closingTime, restrictedOption, longTermOption, activeOnMiax, miaxBboPostingIncrementIndicator, liquidityAcceptanceIncrementIndicator, openingUnderlyingMarketCode, priorityQuoteWidth, reserved8 }, bytes)

@[simp] theorem encode_length (message : SimpleSeriesUpdateMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CallOrPut.encode_length, RestrictedOption.encode_length, LongTermOption.encode_length, ActiveOnMiax.encode_length, MiaxBboPostingIncrementIndicator.encode_length, LiquidityAcceptanceIncrementIndicator.encode_length, OpeningUnderlyingMarketCode.encode_length]

theorem encode_length_pos (message : SimpleSeriesUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleSeriesUpdateMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ActiveOnMiax.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MiaxBboPostingIncrementIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityAcceptanceIncrementIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningUnderlyingMarketCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleSeriesUpdateMessage

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

/-- Simple Top Of Market Bid Compact Message: 15 bytes -/
structure SimpleTopOfMarketBidCompactMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  mbboPrice2 : BitVec 16
  mbboSize2 : BitVec 16
  mbboPriorityCustomerSize2 : BitVec 16
  mbboCondition : MbboCondition
  deriving DecidableEq, Repr

namespace SimpleTopOfMarketBidCompactMessage

def encode (message : SimpleTopOfMarketBidCompactMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.mbboPrice2
    ++ (encodeUIntLE 2 message.mbboSize2
    ++ (encodeUIntLE 2 message.mbboPriorityCustomerSize2
    ++ (MbboCondition.encode message.mbboCondition)))))

def decode (bytes : List UInt8) : Option (SimpleTopOfMarketBidCompactMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (mbboPrice2, bytes) ← decodeUIntLE 2 bytes
  let (mbboSize2, bytes) ← decodeUIntLE 2 bytes
  let (mbboPriorityCustomerSize2, bytes) ← decodeUIntLE 2 bytes
  let (mbboCondition, bytes) ← MbboCondition.decode bytes
  pure ({ nanoseconds, productId, mbboPrice2, mbboSize2, mbboPriorityCustomerSize2, mbboCondition }, bytes)

@[simp] theorem encode_length (message : SimpleTopOfMarketBidCompactMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MbboCondition.encode_length]

theorem encode_length_pos (message : SimpleTopOfMarketBidCompactMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleTopOfMarketBidCompactMessage) (rest : List UInt8) :
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
  rw [MbboCondition.decode_encode, some_bind]
  rfl

end SimpleTopOfMarketBidCompactMessage

/-- Simple Top Of Market Offer Compact Message: 15 bytes -/
structure SimpleTopOfMarketOfferCompactMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  mbboPrice2 : BitVec 16
  mbboSize2 : BitVec 16
  mbboPriorityCustomerSize2 : BitVec 16
  mbboCondition : MbboCondition
  deriving DecidableEq, Repr

namespace SimpleTopOfMarketOfferCompactMessage

def encode (message : SimpleTopOfMarketOfferCompactMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.mbboPrice2
    ++ (encodeUIntLE 2 message.mbboSize2
    ++ (encodeUIntLE 2 message.mbboPriorityCustomerSize2
    ++ (MbboCondition.encode message.mbboCondition)))))

def decode (bytes : List UInt8) : Option (SimpleTopOfMarketOfferCompactMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (mbboPrice2, bytes) ← decodeUIntLE 2 bytes
  let (mbboSize2, bytes) ← decodeUIntLE 2 bytes
  let (mbboPriorityCustomerSize2, bytes) ← decodeUIntLE 2 bytes
  let (mbboCondition, bytes) ← MbboCondition.decode bytes
  pure ({ nanoseconds, productId, mbboPrice2, mbboSize2, mbboPriorityCustomerSize2, mbboCondition }, bytes)

@[simp] theorem encode_length (message : SimpleTopOfMarketOfferCompactMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MbboCondition.encode_length]

theorem encode_length_pos (message : SimpleTopOfMarketOfferCompactMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleTopOfMarketOfferCompactMessage) (rest : List UInt8) :
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
  rw [MbboCondition.decode_encode, some_bind]
  rfl

end SimpleTopOfMarketOfferCompactMessage

/-- Simple Top Of Market Bid Wide Message: 21 bytes -/
structure SimpleTopOfMarketBidWideMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  mbboPrice4 : BitVec 32
  mbboSize4 : BitVec 32
  mbboPriorityCustomerSize4 : BitVec 32
  mbboCondition : MbboCondition
  deriving DecidableEq, Repr

namespace SimpleTopOfMarketBidWideMessage

def encode (message : SimpleTopOfMarketBidWideMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.mbboPrice4
    ++ (encodeUIntLE 4 message.mbboSize4
    ++ (encodeUIntLE 4 message.mbboPriorityCustomerSize4
    ++ (MbboCondition.encode message.mbboCondition)))))

def decode (bytes : List UInt8) : Option (SimpleTopOfMarketBidWideMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (mbboPrice4, bytes) ← decodeUIntLE 4 bytes
  let (mbboSize4, bytes) ← decodeUIntLE 4 bytes
  let (mbboPriorityCustomerSize4, bytes) ← decodeUIntLE 4 bytes
  let (mbboCondition, bytes) ← MbboCondition.decode bytes
  pure ({ nanoseconds, productId, mbboPrice4, mbboSize4, mbboPriorityCustomerSize4, mbboCondition }, bytes)

@[simp] theorem encode_length (message : SimpleTopOfMarketBidWideMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MbboCondition.encode_length]

theorem encode_length_pos (message : SimpleTopOfMarketBidWideMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleTopOfMarketBidWideMessage) (rest : List UInt8) :
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
  rw [MbboCondition.decode_encode, some_bind]
  rfl

end SimpleTopOfMarketBidWideMessage

/-- Simple Top Of Market Offer Wide Message: 21 bytes -/
structure SimpleTopOfMarketOfferWideMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  mbboPrice4 : BitVec 32
  mbboSize4 : BitVec 32
  mbboPriorityCustomerSize4 : BitVec 32
  mbboCondition : MbboCondition
  deriving DecidableEq, Repr

namespace SimpleTopOfMarketOfferWideMessage

def encode (message : SimpleTopOfMarketOfferWideMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.mbboPrice4
    ++ (encodeUIntLE 4 message.mbboSize4
    ++ (encodeUIntLE 4 message.mbboPriorityCustomerSize4
    ++ (MbboCondition.encode message.mbboCondition)))))

def decode (bytes : List UInt8) : Option (SimpleTopOfMarketOfferWideMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (mbboPrice4, bytes) ← decodeUIntLE 4 bytes
  let (mbboSize4, bytes) ← decodeUIntLE 4 bytes
  let (mbboPriorityCustomerSize4, bytes) ← decodeUIntLE 4 bytes
  let (mbboCondition, bytes) ← MbboCondition.decode bytes
  pure ({ nanoseconds, productId, mbboPrice4, mbboSize4, mbboPriorityCustomerSize4, mbboCondition }, bytes)

@[simp] theorem encode_length (message : SimpleTopOfMarketOfferWideMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MbboCondition.encode_length]

theorem encode_length_pos (message : SimpleTopOfMarketOfferWideMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleTopOfMarketOfferWideMessage) (rest : List UInt8) :
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
  rw [MbboCondition.decode_encode, some_bind]
  rfl

end SimpleTopOfMarketOfferWideMessage

/-- Simple Double Sided Top Of Market Compact Message: 22 bytes -/
structure SimpleDoubleSidedTopOfMarketCompactMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  bidPrice2 : BitVec 16
  bidSize2 : BitVec 16
  bidPriorityCustomerSize2 : BitVec 16
  bidCondition : BidCondition
  offerPrice2 : BitVec 16
  offerSize2 : BitVec 16
  offerPriorityCustomerSize2 : BitVec 16
  offerCondition : OfferCondition
  deriving DecidableEq, Repr

namespace SimpleDoubleSidedTopOfMarketCompactMessage

def encode (message : SimpleDoubleSidedTopOfMarketCompactMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.bidPrice2
    ++ (encodeUIntLE 2 message.bidSize2
    ++ (encodeUIntLE 2 message.bidPriorityCustomerSize2
    ++ (BidCondition.encode message.bidCondition
    ++ (encodeUIntLE 2 message.offerPrice2
    ++ (encodeUIntLE 2 message.offerSize2
    ++ (encodeUIntLE 2 message.offerPriorityCustomerSize2
    ++ (OfferCondition.encode message.offerCondition)))))))))

def decode (bytes : List UInt8) : Option (SimpleDoubleSidedTopOfMarketCompactMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice2, bytes) ← decodeUIntLE 2 bytes
  let (bidSize2, bytes) ← decodeUIntLE 2 bytes
  let (bidPriorityCustomerSize2, bytes) ← decodeUIntLE 2 bytes
  let (bidCondition, bytes) ← BidCondition.decode bytes
  let (offerPrice2, bytes) ← decodeUIntLE 2 bytes
  let (offerSize2, bytes) ← decodeUIntLE 2 bytes
  let (offerPriorityCustomerSize2, bytes) ← decodeUIntLE 2 bytes
  let (offerCondition, bytes) ← OfferCondition.decode bytes
  pure ({ nanoseconds, productId, bidPrice2, bidSize2, bidPriorityCustomerSize2, bidCondition, offerPrice2, offerSize2, offerPriorityCustomerSize2, offerCondition }, bytes)

@[simp] theorem encode_length (message : SimpleDoubleSidedTopOfMarketCompactMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, BidCondition.encode_length, OfferCondition.encode_length]

theorem encode_length_pos (message : SimpleDoubleSidedTopOfMarketCompactMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleDoubleSidedTopOfMarketCompactMessage) (rest : List UInt8) :
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

end SimpleDoubleSidedTopOfMarketCompactMessage

/-- Simple Double Sided Top Of Market Wide Message: 34 bytes -/
structure SimpleDoubleSidedTopOfMarketWideMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  bidPrice4 : BitVec 32
  bidSize4 : BitVec 32
  bidPriorityCustomerSize4 : BitVec 32
  bidCondition : BidCondition
  offerPrice4 : BitVec 32
  offerSize4 : BitVec 32
  offerPriorityCustomerSize4 : BitVec 32
  offerCondition : OfferCondition
  deriving DecidableEq, Repr

namespace SimpleDoubleSidedTopOfMarketWideMessage

def encode (message : SimpleDoubleSidedTopOfMarketWideMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.bidPrice4
    ++ (encodeUIntLE 4 message.bidSize4
    ++ (encodeUIntLE 4 message.bidPriorityCustomerSize4
    ++ (BidCondition.encode message.bidCondition
    ++ (encodeUIntLE 4 message.offerPrice4
    ++ (encodeUIntLE 4 message.offerSize4
    ++ (encodeUIntLE 4 message.offerPriorityCustomerSize4
    ++ (OfferCondition.encode message.offerCondition)))))))))

def decode (bytes : List UInt8) : Option (SimpleDoubleSidedTopOfMarketWideMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice4, bytes) ← decodeUIntLE 4 bytes
  let (bidSize4, bytes) ← decodeUIntLE 4 bytes
  let (bidPriorityCustomerSize4, bytes) ← decodeUIntLE 4 bytes
  let (bidCondition, bytes) ← BidCondition.decode bytes
  let (offerPrice4, bytes) ← decodeUIntLE 4 bytes
  let (offerSize4, bytes) ← decodeUIntLE 4 bytes
  let (offerPriorityCustomerSize4, bytes) ← decodeUIntLE 4 bytes
  let (offerCondition, bytes) ← OfferCondition.decode bytes
  pure ({ nanoseconds, productId, bidPrice4, bidSize4, bidPriorityCustomerSize4, bidCondition, offerPrice4, offerSize4, offerPriorityCustomerSize4, offerCondition }, bytes)

@[simp] theorem encode_length (message : SimpleDoubleSidedTopOfMarketWideMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, BidCondition.encode_length, OfferCondition.encode_length]

theorem encode_length_pos (message : SimpleDoubleSidedTopOfMarketWideMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleDoubleSidedTopOfMarketWideMessage) (rest : List UInt8) :
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

end SimpleDoubleSidedTopOfMarketWideMessage

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
  expectedEventTimeSeconds : BitVec 32
  expectedEventTimeNanoSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace UnderlyingTradingStatusNotificationMessage

def encode (message : UnderlyingTradingStatusNotificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.underlyingSymbol
    ++ (TradingStatus.encode message.tradingStatus
    ++ (EventReason.encode message.eventReason
    ++ (encodeUIntLE 4 message.expectedEventTimeSeconds
    ++ (encodeUIntLE 4 message.expectedEventTimeNanoSeconds)))))

def decode (bytes : List UInt8) : Option (UnderlyingTradingStatusNotificationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (eventReason, bytes) ← EventReason.decode bytes
  let (expectedEventTimeSeconds, bytes) ← decodeUIntLE 4 bytes
  let (expectedEventTimeNanoSeconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ nanoseconds, underlyingSymbol, tradingStatus, eventReason, expectedEventTimeSeconds, expectedEventTimeNanoSeconds }, bytes)

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
  | simpleSeriesUpdateMessage (message : SimpleSeriesUpdateMessage) -- "P" 0x50
  | systemStateMessage (message : SystemStateMessage) -- "S" 0x53
  | simpleTopOfMarketBidCompactMessage (message : SimpleTopOfMarketBidCompactMessage) -- "B" 0x42
  | simpleTopOfMarketOfferCompactMessage (message : SimpleTopOfMarketOfferCompactMessage) -- "O" 0x4F
  | simpleTopOfMarketBidWideMessage (message : SimpleTopOfMarketBidWideMessage) -- "W" 0x57
  | simpleTopOfMarketOfferWideMessage (message : SimpleTopOfMarketOfferWideMessage) -- "A" 0x41
  | simpleDoubleSidedTopOfMarketCompactMessage (message : SimpleDoubleSidedTopOfMarketCompactMessage) -- "d" 0x64
  | simpleDoubleSidedTopOfMarketWideMessage (message : SimpleDoubleSidedTopOfMarketWideMessage) -- "D" 0x44
  | lastSaleMessage (message : LastSaleMessage) -- "T" 0x54
  | tradeCancelMessage (message : TradeCancelMessage) -- "X" 0x58
  | underlyingTradingStatusNotificationMessage (message : UnderlyingTradingStatusNotificationMessage) -- "H" 0x48
  deriving DecidableEq, Repr

namespace Data

/-- The Message Type each message is sent under -/
def tag : Data → BitVec 8
  | .systemTimeMessage _ => 49
  | .simpleSeriesUpdateMessage _ => 80
  | .systemStateMessage _ => 83
  | .simpleTopOfMarketBidCompactMessage _ => 66
  | .simpleTopOfMarketOfferCompactMessage _ => 79
  | .simpleTopOfMarketBidWideMessage _ => 87
  | .simpleTopOfMarketOfferWideMessage _ => 65
  | .simpleDoubleSidedTopOfMarketCompactMessage _ => 100
  | .simpleDoubleSidedTopOfMarketWideMessage _ => 68
  | .lastSaleMessage _ => 84
  | .tradeCancelMessage _ => 88
  | .underlyingTradingStatusNotificationMessage _ => 72

def encode : Data → List UInt8
  | .systemTimeMessage message => SystemTimeMessage.encode message
  | .simpleSeriesUpdateMessage message => SimpleSeriesUpdateMessage.encode message
  | .systemStateMessage message => SystemStateMessage.encode message
  | .simpleTopOfMarketBidCompactMessage message => SimpleTopOfMarketBidCompactMessage.encode message
  | .simpleTopOfMarketOfferCompactMessage message => SimpleTopOfMarketOfferCompactMessage.encode message
  | .simpleTopOfMarketBidWideMessage message => SimpleTopOfMarketBidWideMessage.encode message
  | .simpleTopOfMarketOfferWideMessage message => SimpleTopOfMarketOfferWideMessage.encode message
  | .simpleDoubleSidedTopOfMarketCompactMessage message => SimpleDoubleSidedTopOfMarketCompactMessage.encode message
  | .simpleDoubleSidedTopOfMarketWideMessage message => SimpleDoubleSidedTopOfMarketWideMessage.encode message
  | .lastSaleMessage message => LastSaleMessage.encode message
  | .tradeCancelMessage message => TradeCancelMessage.encode message
  | .underlyingTradingStatusNotificationMessage message => UnderlyingTradingStatusNotificationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Data) : (encode message).length ≤ 72 := by
  cases message with
  | systemTimeMessage inner =>
    simp only [encode, SystemTimeMessage.encode_length]
    omega
  | simpleSeriesUpdateMessage inner =>
    simp only [encode, SimpleSeriesUpdateMessage.encode_length]
    omega
  | systemStateMessage inner =>
    simp only [encode, SystemStateMessage.encode_length]
    omega
  | simpleTopOfMarketBidCompactMessage inner =>
    simp only [encode, SimpleTopOfMarketBidCompactMessage.encode_length]
    omega
  | simpleTopOfMarketOfferCompactMessage inner =>
    simp only [encode, SimpleTopOfMarketOfferCompactMessage.encode_length]
    omega
  | simpleTopOfMarketBidWideMessage inner =>
    simp only [encode, SimpleTopOfMarketBidWideMessage.encode_length]
    omega
  | simpleTopOfMarketOfferWideMessage inner =>
    simp only [encode, SimpleTopOfMarketOfferWideMessage.encode_length]
    omega
  | simpleDoubleSidedTopOfMarketCompactMessage inner =>
    simp only [encode, SimpleDoubleSidedTopOfMarketCompactMessage.encode_length]
    omega
  | simpleDoubleSidedTopOfMarketWideMessage inner =>
    simp only [encode, SimpleDoubleSidedTopOfMarketWideMessage.encode_length]
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
  else if tag = 80 then (SimpleSeriesUpdateMessage.decode bytes).map fun (message, rest) => (.simpleSeriesUpdateMessage message, rest)
  else if tag = 83 then (SystemStateMessage.decode bytes).map fun (message, rest) => (.systemStateMessage message, rest)
  else if tag = 66 then (SimpleTopOfMarketBidCompactMessage.decode bytes).map fun (message, rest) => (.simpleTopOfMarketBidCompactMessage message, rest)
  else if tag = 79 then (SimpleTopOfMarketOfferCompactMessage.decode bytes).map fun (message, rest) => (.simpleTopOfMarketOfferCompactMessage message, rest)
  else if tag = 87 then (SimpleTopOfMarketBidWideMessage.decode bytes).map fun (message, rest) => (.simpleTopOfMarketBidWideMessage message, rest)
  else if tag = 65 then (SimpleTopOfMarketOfferWideMessage.decode bytes).map fun (message, rest) => (.simpleTopOfMarketOfferWideMessage message, rest)
  else if tag = 100 then (SimpleDoubleSidedTopOfMarketCompactMessage.decode bytes).map fun (message, rest) => (.simpleDoubleSidedTopOfMarketCompactMessage message, rest)
  else if tag = 68 then (SimpleDoubleSidedTopOfMarketWideMessage.decode bytes).map fun (message, rest) => (.simpleDoubleSidedTopOfMarketWideMessage message, rest)
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
  | simpleSeriesUpdateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SimpleSeriesUpdateMessage.encode_length]
    omega
  | systemStateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SystemStateMessage.encode_length]
    omega
  | simpleTopOfMarketBidCompactMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SimpleTopOfMarketBidCompactMessage.encode_length]
    omega
  | simpleTopOfMarketOfferCompactMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SimpleTopOfMarketOfferCompactMessage.encode_length]
    omega
  | simpleTopOfMarketBidWideMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SimpleTopOfMarketBidWideMessage.encode_length]
    omega
  | simpleTopOfMarketOfferWideMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SimpleTopOfMarketOfferWideMessage.encode_length]
    omega
  | simpleDoubleSidedTopOfMarketCompactMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SimpleDoubleSidedTopOfMarketCompactMessage.encode_length]
    omega
  | simpleDoubleSidedTopOfMarketWideMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SimpleDoubleSidedTopOfMarketWideMessage.encode_length]
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

/-- Packet -/
structure Packet where
  machMessage : List MachMessage
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany MachMessage.encode message.machMessage

def decode (bytes : List UInt8) : Option Packet := do
  let machMessage ← decodeAll MachMessage.decode bytes.length bytes
  pure { machMessage }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany MachMessage.encode MachMessage.decode MachMessage.decode_encode MachMessage.encode_length_pos message.machMessage _ (encodeMany_length_ge MachMessage.encode MachMessage.encode_length_pos message.machMessage), some_bind]
  rfl

end Packet

end Omi.MiaxPearloptionsTopofmarketMachV22
