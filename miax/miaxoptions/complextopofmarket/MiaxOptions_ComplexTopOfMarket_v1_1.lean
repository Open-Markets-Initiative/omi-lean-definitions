import Omi.Wire

/-!
# Miami International Holdings Complex Top Of Market v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Application Message is not framed: its length Packet Length is not an integer it reads.

Note: Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxMiaxoptionsComplextopofmarketMachV11

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
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ RestrictedOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RestrictedOption

def toByte : RestrictedOption → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RestrictedOption :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : RestrictedOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RestrictedOption) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
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
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ LongTermOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LongTermOption

def toByte : LongTermOption → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LongTermOption :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : LongTermOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LongTermOption) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
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
  | nickel -- Nickel
  | dime -- Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ MiaxBboPostingIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MiaxBboPostingIncrementIndicator

def toByte : MiaxBboPostingIncrementIndicator → UInt8
  | .penny => 0x50
  | .nickel => 0x4E
  | .dime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MiaxBboPostingIncrementIndicator :=
  if byte = 0x50 then .penny
  else if byte = 0x4E then .nickel
  else .dime

def ofByte (byte : UInt8) : MiaxBboPostingIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MiaxBboPostingIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny => decide
  | nickel => decide
  | dime => decide
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
  | nickel -- Nickel
  | dime -- Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityAcceptanceIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityAcceptanceIncrementIndicator

def toByte : LiquidityAcceptanceIncrementIndicator → UInt8
  | .penny => 0x50
  | .nickel => 0x4E
  | .dime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityAcceptanceIncrementIndicator :=
  if byte = 0x50 then .penny
  else if byte = 0x4E then .nickel
  else .dime

def ofByte (byte : UInt8) : LiquidityAcceptanceIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityAcceptanceIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny => decide
  | nickel => decide
  | dime => decide
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

/-- Update Reason: one byte code -/
def UpdateReason.codes : List UInt8 :=
  [0x4E, 0x55]

inductive UpdateReason where
  | newStrategyCreated -- New Strategy Created
  | updated -- Updated
  | unlisted (byte : { byte : UInt8 // byte ∉ UpdateReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UpdateReason

def toByte : UpdateReason → UInt8
  | .newStrategyCreated => 0x4E
  | .updated => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UpdateReason :=
  if byte = 0x4E then .newStrategyCreated
  else .updated

def ofByte (byte : UInt8) : UpdateReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UpdateReason) : ofByte value.toByte = value := by
  cases value with
  | newStrategyCreated => decide
  | updated => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UpdateReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UpdateReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UpdateReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : UpdateReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UpdateReason

/-- Leg Side: one byte code -/
def LegSide.codes : List UInt8 :=
  [0x42, 0x41]

inductive LegSide where
  | bid -- Bid
  | ask -- Ask
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide

def toByte : LegSide → UInt8
  | .bid => 0x42
  | .ask => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide :=
  if byte = 0x42 then .bid
  else .ask

def ofByte (byte : UInt8) : LegSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | ask => decide
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

/-- Top Of Market Quote Condition: one byte code -/
def TopOfMarketQuoteCondition.codes : List UInt8 :=
  [0x48, 0x52, 0x4F]

inductive TopOfMarketQuoteCondition where
  | halted -- Halted
  | resumed -- Resumed
  | opened -- Opened
  | unlisted (byte : { byte : UInt8 // byte ∉ TopOfMarketQuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TopOfMarketQuoteCondition

def toByte : TopOfMarketQuoteCondition → UInt8
  | .halted => 0x48
  | .resumed => 0x52
  | .opened => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TopOfMarketQuoteCondition :=
  if byte = 0x48 then .halted
  else if byte = 0x52 then .resumed
  else .opened

def ofByte (byte : UInt8) : TopOfMarketQuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TopOfMarketQuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | resumed => decide
  | opened => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TopOfMarketQuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TopOfMarketQuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TopOfMarketQuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TopOfMarketQuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TopOfMarketQuoteCondition

/-- Bid Condition: one byte code -/
def BidCondition.codes : List UInt8 :=
  [0x41, 0x54, 0x57, 0x53, 0x43, 0x4D, 0x4C]

inductive BidCondition where
  | regular -- Regular
  | tradingHalt -- Trading Halt
  | wide -- Wide
  | simpleAuction -- Simple Auction
  | complexAuction -- Complex Auction
  | simpleMarketProtection -- Simple Market Protection
  | legMarketProtection -- Leg Market Protection
  | unlisted (byte : { byte : UInt8 // byte ∉ BidCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BidCondition

def toByte : BidCondition → UInt8
  | .regular => 0x41
  | .tradingHalt => 0x54
  | .wide => 0x57
  | .simpleAuction => 0x53
  | .complexAuction => 0x43
  | .simpleMarketProtection => 0x4D
  | .legMarketProtection => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BidCondition :=
  if byte = 0x41 then .regular
  else if byte = 0x54 then .tradingHalt
  else if byte = 0x57 then .wide
  else if byte = 0x53 then .simpleAuction
  else if byte = 0x43 then .complexAuction
  else if byte = 0x4D then .simpleMarketProtection
  else .legMarketProtection

def ofByte (byte : UInt8) : BidCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BidCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | tradingHalt => decide
  | wide => decide
  | simpleAuction => decide
  | complexAuction => decide
  | simpleMarketProtection => decide
  | legMarketProtection => decide
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
  [0x41, 0x54, 0x57, 0x53, 0x43, 0x4D, 0x4C]

inductive OfferCondition where
  | regular -- Regular
  | tradingHalt -- Trading Halt
  | wide -- Wide
  | simpleAuction -- Simple Auction
  | complexAuction -- Complex Auction
  | simpleMarketProtection -- Simple Market Protection
  | legMarketProtection -- Leg Market Protection
  | unlisted (byte : { byte : UInt8 // byte ∉ OfferCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OfferCondition

def toByte : OfferCondition → UInt8
  | .regular => 0x41
  | .tradingHalt => 0x54
  | .wide => 0x57
  | .simpleAuction => 0x53
  | .complexAuction => 0x43
  | .simpleMarketProtection => 0x4D
  | .legMarketProtection => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OfferCondition :=
  if byte = 0x41 then .regular
  else if byte = 0x54 then .tradingHalt
  else if byte = 0x57 then .wide
  else if byte = 0x53 then .simpleAuction
  else if byte = 0x43 then .complexAuction
  else if byte = 0x4D then .simpleMarketProtection
  else .legMarketProtection

def ofByte (byte : UInt8) : OfferCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OfferCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | tradingHalt => decide
  | wide => decide
  | simpleAuction => decide
  | complexAuction => decide
  | simpleMarketProtection => decide
  | legMarketProtection => decide
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
  [0x53, 0x4C]

inductive TradeCondition where
  | matched -- Matched
  | legged -- Legged
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCondition

def toByte : TradeCondition → UInt8
  | .matched => 0x53
  | .legged => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCondition :=
  if byte = 0x53 then .matched
  else .legged

def ofByte (byte : UInt8) : TradeCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCondition) : ofByte value.toByte = value := by
  cases value with
  | matched => decide
  | legged => decide
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

/-- Series Update: 72 bytes -/
structure SeriesUpdate where
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

namespace SeriesUpdate

def encode (message : SeriesUpdate) : List UInt8 :=
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

def decode (bytes : List UInt8) : Option (SeriesUpdate × List UInt8) := do
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

@[simp] theorem encode_length (message : SeriesUpdate) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CallOrPut.encode_length, RestrictedOption.encode_length, LongTermOption.encode_length, ActiveOnMiax.encode_length, MiaxBboPostingIncrementIndicator.encode_length, LiquidityAcceptanceIncrementIndicator.encode_length, OpeningUnderlyingMarketCode.encode_length]

theorem encode_length_pos (message : SeriesUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesUpdate) (rest : List UInt8) :
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

end SeriesUpdate

/-- Leg Definition: 15 bytes -/
structure LegDefinition where
  productId : BitVec 32
  legRatioQty : BitVec 16
  legSide : LegSide
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace LegDefinition

def encode (message : LegDefinition) : List UInt8 :=
  encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.legRatioQty
    ++ (LegSide.encode message.legSide
    ++ (Alpha.encode message.reserved8)))

def decode (bytes : List UInt8) : Option (LegDefinition × List UInt8) := do
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 2 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ productId, legRatioQty, legSide, reserved8 }, bytes)

@[simp] theorem encode_length (message : LegDefinition) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, LegSide.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : LegDefinition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegDefinition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LegDefinition

/-- Complex Strategy Definition Message -/
structure ComplexStrategyDefinitionMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  underlyingSymbol : Alpha 11
  activeOnMiax : ActiveOnMiax
  reserved1 : Alpha 1
  updateReason : UpdateReason
  reserved10 : Alpha 10
  legDefinition : Bounded 1 LegDefinition
  deriving DecidableEq, Repr

namespace ComplexStrategyDefinitionMessage

def encode (message : ComplexStrategyDefinitionMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (ActiveOnMiax.encode message.activeOnMiax
    ++ (Alpha.encode message.reserved1
    ++ (UpdateReason.encode message.updateReason
    ++ (Alpha.encode message.reserved10
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.legDefinition.val.length)
    ++ (encodeMany LegDefinition.encode message.legDefinition.val))))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyDefinitionMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (activeOnMiax, bytes) ← ActiveOnMiax.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (updateReason, bytes) ← UpdateReason.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (numberOfLegs, bytes) ← decodeUIntLE 1 bytes
  let (legDefinition_, bytes) ← decodeMany LegDefinition.decode numberOfLegs.toNat bytes
  if fits_legDefinition : legDefinition_.length < 256 ^ 1 then
    pure ({ nanoseconds, strategyId, underlyingSymbol, activeOnMiax, reserved1, updateReason, reserved10, legDefinition := ⟨legDefinition_, fits_legDefinition⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexStrategyDefinitionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexStrategyDefinitionMessage) : (encode message).length ≤ 3858 := by
  have bound_legDefinition := message.legDefinition.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, ActiveOnMiax.encode_length, UpdateReason.encode_length, encodeMany_length_const LegDefinition.encode 15 LegDefinition.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexStrategyDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ActiveOnMiax.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UpdateReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegDefinition.encode LegDefinition.decode LegDefinition.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legDefinition.length_lt]
  rfl

end ComplexStrategyDefinitionMessage

/-- System State Message: 17 bytes -/
structure SystemStateMessage where
  nanoseconds : BitVec 32
  cToMVersion : Alpha 8
  sessionId : BitVec 32
  systemStatus : SystemStatus
  deriving DecidableEq, Repr

namespace SystemStateMessage

def encode (message : SystemStateMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.cToMVersion
    ++ (encodeUIntLE 4 message.sessionId
    ++ (SystemStatus.encode message.systemStatus)))

def decode (bytes : List UInt8) : Option (SystemStateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (cToMVersion, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  pure ({ nanoseconds, cToMVersion, sessionId, systemStatus }, bytes)

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

/-- Compact Complex Top Of Market Bid Message: 13 bytes -/
structure CompactComplexTopOfMarketBidMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  compactPrice : BitVec 16
  compactSize : BitVec 16
  topOfMarketQuoteCondition : TopOfMarketQuoteCondition
  deriving DecidableEq, Repr

namespace CompactComplexTopOfMarketBidMessage

def encode (message : CompactComplexTopOfMarketBidMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (encodeUIntLE 2 message.compactPrice
    ++ (encodeUIntLE 2 message.compactSize
    ++ (TopOfMarketQuoteCondition.encode message.topOfMarketQuoteCondition))))

def decode (bytes : List UInt8) : Option (CompactComplexTopOfMarketBidMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (compactPrice, bytes) ← decodeUIntLE 2 bytes
  let (compactSize, bytes) ← decodeUIntLE 2 bytes
  let (topOfMarketQuoteCondition, bytes) ← TopOfMarketQuoteCondition.decode bytes
  pure ({ nanoseconds, strategyId, compactPrice, compactSize, topOfMarketQuoteCondition }, bytes)

@[simp] theorem encode_length (message : CompactComplexTopOfMarketBidMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TopOfMarketQuoteCondition.encode_length]

theorem encode_length_pos (message : CompactComplexTopOfMarketBidMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CompactComplexTopOfMarketBidMessage) (rest : List UInt8) :
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
  rw [TopOfMarketQuoteCondition.decode_encode, some_bind]
  rfl

end CompactComplexTopOfMarketBidMessage

/-- Compact Complex Top Of Market Offer Message: 15 bytes -/
structure CompactComplexTopOfMarketOfferMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  compactPrice : BitVec 16
  compactSize : BitVec 16
  reserved2 : Alpha 2
  topOfMarketQuoteCondition : TopOfMarketQuoteCondition
  deriving DecidableEq, Repr

namespace CompactComplexTopOfMarketOfferMessage

def encode (message : CompactComplexTopOfMarketOfferMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (encodeUIntLE 2 message.compactPrice
    ++ (encodeUIntLE 2 message.compactSize
    ++ (Alpha.encode message.reserved2
    ++ (TopOfMarketQuoteCondition.encode message.topOfMarketQuoteCondition)))))

def decode (bytes : List UInt8) : Option (CompactComplexTopOfMarketOfferMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (compactPrice, bytes) ← decodeUIntLE 2 bytes
  let (compactSize, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (topOfMarketQuoteCondition, bytes) ← TopOfMarketQuoteCondition.decode bytes
  pure ({ nanoseconds, strategyId, compactPrice, compactSize, reserved2, topOfMarketQuoteCondition }, bytes)

@[simp] theorem encode_length (message : CompactComplexTopOfMarketOfferMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TopOfMarketQuoteCondition.encode_length]

theorem encode_length_pos (message : CompactComplexTopOfMarketOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CompactComplexTopOfMarketOfferMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TopOfMarketQuoteCondition.decode_encode, some_bind]
  rfl

end CompactComplexTopOfMarketOfferMessage

/-- Wide Complex Top Of Market Bid Message: 25 bytes -/
structure WideComplexTopOfMarketBidMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  widePrice : BitVec 64
  wideSize : BitVec 32
  reserved4 : Alpha 4
  topOfMarketQuoteCondition : TopOfMarketQuoteCondition
  deriving DecidableEq, Repr

namespace WideComplexTopOfMarketBidMessage

def encode (message : WideComplexTopOfMarketBidMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (encodeUIntLE 8 message.widePrice
    ++ (encodeUIntLE 4 message.wideSize
    ++ (Alpha.encode message.reserved4
    ++ (TopOfMarketQuoteCondition.encode message.topOfMarketQuoteCondition)))))

def decode (bytes : List UInt8) : Option (WideComplexTopOfMarketBidMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (widePrice, bytes) ← decodeUIntLE 8 bytes
  let (wideSize, bytes) ← decodeUIntLE 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (topOfMarketQuoteCondition, bytes) ← TopOfMarketQuoteCondition.decode bytes
  pure ({ nanoseconds, strategyId, widePrice, wideSize, reserved4, topOfMarketQuoteCondition }, bytes)

@[simp] theorem encode_length (message : WideComplexTopOfMarketBidMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TopOfMarketQuoteCondition.encode_length]

theorem encode_length_pos (message : WideComplexTopOfMarketBidMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WideComplexTopOfMarketBidMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TopOfMarketQuoteCondition.decode_encode, some_bind]
  rfl

end WideComplexTopOfMarketBidMessage

/-- Wide Complex Top Of Market Offer Message: 25 bytes -/
structure WideComplexTopOfMarketOfferMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  widePrice : BitVec 64
  wideSize : BitVec 32
  reserved4 : Alpha 4
  topOfMarketQuoteCondition : TopOfMarketQuoteCondition
  deriving DecidableEq, Repr

namespace WideComplexTopOfMarketOfferMessage

def encode (message : WideComplexTopOfMarketOfferMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (encodeUIntLE 8 message.widePrice
    ++ (encodeUIntLE 4 message.wideSize
    ++ (Alpha.encode message.reserved4
    ++ (TopOfMarketQuoteCondition.encode message.topOfMarketQuoteCondition)))))

def decode (bytes : List UInt8) : Option (WideComplexTopOfMarketOfferMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (widePrice, bytes) ← decodeUIntLE 8 bytes
  let (wideSize, bytes) ← decodeUIntLE 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (topOfMarketQuoteCondition, bytes) ← TopOfMarketQuoteCondition.decode bytes
  pure ({ nanoseconds, strategyId, widePrice, wideSize, reserved4, topOfMarketQuoteCondition }, bytes)

@[simp] theorem encode_length (message : WideComplexTopOfMarketOfferMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TopOfMarketQuoteCondition.encode_length]

theorem encode_length_pos (message : WideComplexTopOfMarketOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WideComplexTopOfMarketOfferMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TopOfMarketQuoteCondition.decode_encode, some_bind]
  rfl

end WideComplexTopOfMarketOfferMessage

/-- Compact Bid: 7 bytes -/
structure CompactBid where
  compactBidPrice : BitVec 16
  compactBidSize : BitVec 16
  reserved2 : Alpha 2
  bidCondition : BidCondition
  deriving DecidableEq, Repr

namespace CompactBid

def encode (message : CompactBid) : List UInt8 :=
  encodeUIntLE 2 message.compactBidPrice
    ++ (encodeUIntLE 2 message.compactBidSize
    ++ (Alpha.encode message.reserved2
    ++ (BidCondition.encode message.bidCondition)))

def decode (bytes : List UInt8) : Option (CompactBid × List UInt8) := do
  let (compactBidPrice, bytes) ← decodeUIntLE 2 bytes
  let (compactBidSize, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (bidCondition, bytes) ← BidCondition.decode bytes
  pure ({ compactBidPrice, compactBidSize, reserved2, bidCondition }, bytes)

@[simp] theorem encode_length (message : CompactBid) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, BidCondition.encode_length]

theorem encode_length_pos (message : CompactBid) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CompactBid) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [BidCondition.decode_encode, some_bind]
  rfl

end CompactBid

/-- Compact Offer: 7 bytes -/
structure CompactOffer where
  compactOfferPrice : BitVec 16
  compactOfferSize : BitVec 16
  reserved2 : Alpha 2
  offerCondition : OfferCondition
  deriving DecidableEq, Repr

namespace CompactOffer

def encode (message : CompactOffer) : List UInt8 :=
  encodeUIntLE 2 message.compactOfferPrice
    ++ (encodeUIntLE 2 message.compactOfferSize
    ++ (Alpha.encode message.reserved2
    ++ (OfferCondition.encode message.offerCondition)))

def decode (bytes : List UInt8) : Option (CompactOffer × List UInt8) := do
  let (compactOfferPrice, bytes) ← decodeUIntLE 2 bytes
  let (compactOfferSize, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (offerCondition, bytes) ← OfferCondition.decode bytes
  pure ({ compactOfferPrice, compactOfferSize, reserved2, offerCondition }, bytes)

@[simp] theorem encode_length (message : CompactOffer) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OfferCondition.encode_length]

theorem encode_length_pos (message : CompactOffer) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CompactOffer) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [OfferCondition.decode_encode, some_bind]
  rfl

end CompactOffer

/-- Compact Complex Double Sided Top Of Market Message: 22 bytes -/
structure CompactComplexDoubleSidedTopOfMarketMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  compactBid : CompactBid
  compactOffer : CompactOffer
  deriving DecidableEq, Repr

namespace CompactComplexDoubleSidedTopOfMarketMessage

def encode (message : CompactComplexDoubleSidedTopOfMarketMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (CompactBid.encode message.compactBid
    ++ (CompactOffer.encode message.compactOffer)))

def decode (bytes : List UInt8) : Option (CompactComplexDoubleSidedTopOfMarketMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (compactBid, bytes) ← CompactBid.decode bytes
  let (compactOffer, bytes) ← CompactOffer.decode bytes
  pure ({ nanoseconds, strategyId, compactBid, compactOffer }, bytes)

@[simp] theorem encode_length (message : CompactComplexDoubleSidedTopOfMarketMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, CompactBid.encode_length, CompactOffer.encode_length]

theorem encode_length_pos (message : CompactComplexDoubleSidedTopOfMarketMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CompactComplexDoubleSidedTopOfMarketMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CompactBid.decode_encode, some_bind]
  dsimp only
  rw [CompactOffer.decode_encode, some_bind]
  rfl

end CompactComplexDoubleSidedTopOfMarketMessage

/-- Wide Bid: 17 bytes -/
structure WideBid where
  wideBidPrice : BitVec 64
  wideBidSize : BitVec 32
  reserved4 : Alpha 4
  bidCondition : BidCondition
  deriving DecidableEq, Repr

namespace WideBid

def encode (message : WideBid) : List UInt8 :=
  encodeUIntLE 8 message.wideBidPrice
    ++ (encodeUIntLE 4 message.wideBidSize
    ++ (Alpha.encode message.reserved4
    ++ (BidCondition.encode message.bidCondition)))

def decode (bytes : List UInt8) : Option (WideBid × List UInt8) := do
  let (wideBidPrice, bytes) ← decodeUIntLE 8 bytes
  let (wideBidSize, bytes) ← decodeUIntLE 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (bidCondition, bytes) ← BidCondition.decode bytes
  pure ({ wideBidPrice, wideBidSize, reserved4, bidCondition }, bytes)

@[simp] theorem encode_length (message : WideBid) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, BidCondition.encode_length]

theorem encode_length_pos (message : WideBid) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WideBid) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [BidCondition.decode_encode, some_bind]
  rfl

end WideBid

/-- Wide Offer: 17 bytes -/
structure WideOffer where
  wideOfferPrice : BitVec 64
  wideOfferSize : BitVec 32
  reserved4 : Alpha 4
  offerCondition : OfferCondition
  deriving DecidableEq, Repr

namespace WideOffer

def encode (message : WideOffer) : List UInt8 :=
  encodeUIntLE 8 message.wideOfferPrice
    ++ (encodeUIntLE 4 message.wideOfferSize
    ++ (Alpha.encode message.reserved4
    ++ (OfferCondition.encode message.offerCondition)))

def decode (bytes : List UInt8) : Option (WideOffer × List UInt8) := do
  let (wideOfferPrice, bytes) ← decodeUIntLE 8 bytes
  let (wideOfferSize, bytes) ← decodeUIntLE 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (offerCondition, bytes) ← OfferCondition.decode bytes
  pure ({ wideOfferPrice, wideOfferSize, reserved4, offerCondition }, bytes)

@[simp] theorem encode_length (message : WideOffer) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OfferCondition.encode_length]

theorem encode_length_pos (message : WideOffer) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WideOffer) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [OfferCondition.decode_encode, some_bind]
  rfl

end WideOffer

/-- Wide Complex Double Sided Top Of Market Message: 42 bytes -/
structure WideComplexDoubleSidedTopOfMarketMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  wideBid : WideBid
  wideOffer : WideOffer
  deriving DecidableEq, Repr

namespace WideComplexDoubleSidedTopOfMarketMessage

def encode (message : WideComplexDoubleSidedTopOfMarketMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (WideBid.encode message.wideBid
    ++ (WideOffer.encode message.wideOffer)))

def decode (bytes : List UInt8) : Option (WideComplexDoubleSidedTopOfMarketMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (wideBid, bytes) ← WideBid.decode bytes
  let (wideOffer, bytes) ← WideOffer.decode bytes
  pure ({ nanoseconds, strategyId, wideBid, wideOffer }, bytes)

@[simp] theorem encode_length (message : WideComplexDoubleSidedTopOfMarketMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, WideBid.encode_length, WideOffer.encode_length]

theorem encode_length_pos (message : WideComplexDoubleSidedTopOfMarketMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WideComplexDoubleSidedTopOfMarketMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, WideBid.decode_encode, some_bind]
  dsimp only
  rw [WideOffer.decode_encode, some_bind]
  rfl

end WideComplexDoubleSidedTopOfMarketMessage

/-- Strategy Trade Message: 41 bytes -/
structure StrategyTradeMessage where
  nanoseconds : BitVec 32
  strategyId : BitVec 32
  tradeId : BitVec 32
  netPrice : BitVec 64
  tradeSize : BitVec 32
  tradeCondition : TradeCondition
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace StrategyTradeMessage

def encode (message : StrategyTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.strategyId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 8 message.netPrice
    ++ (encodeUIntLE 4 message.tradeSize
    ++ (TradeCondition.encode message.tradeCondition
    ++ (Alpha.encode message.reserved16))))))

def decode (bytes : List UInt8) : Option (StrategyTradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (netPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradeSize, bytes) ← decodeUIntLE 4 bytes
  let (tradeCondition, bytes) ← TradeCondition.decode bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ nanoseconds, strategyId, tradeId, netPrice, tradeSize, tradeCondition, reserved16 }, bytes)

@[simp] theorem encode_length (message : StrategyTradeMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCondition.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StrategyTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeCondition.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeMessage

/-- Underlying Trading Status Message: 25 bytes -/
structure UnderlyingTradingStatusMessage where
  nanoseconds : BitVec 32
  underlyingSymbol : Alpha 11
  tradingStatus : TradingStatus
  eventReason : EventReason
  secondsPart : BitVec 32
  expectedEventTimeNanoSecondsPart : BitVec 32
  deriving DecidableEq, Repr

namespace UnderlyingTradingStatusMessage

def encode (message : UnderlyingTradingStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.underlyingSymbol
    ++ (TradingStatus.encode message.tradingStatus
    ++ (EventReason.encode message.eventReason
    ++ (encodeUIntLE 4 message.secondsPart
    ++ (encodeUIntLE 4 message.expectedEventTimeNanoSecondsPart)))))

def decode (bytes : List UInt8) : Option (UnderlyingTradingStatusMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (eventReason, bytes) ← EventReason.decode bytes
  let (secondsPart, bytes) ← decodeUIntLE 4 bytes
  let (expectedEventTimeNanoSecondsPart, bytes) ← decodeUIntLE 4 bytes
  pure ({ nanoseconds, underlyingSymbol, tradingStatus, eventReason, secondsPart, expectedEventTimeNanoSecondsPart }, bytes)

@[simp] theorem encode_length (message : UnderlyingTradingStatusMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradingStatus.encode_length, EventReason.encode_length]

theorem encode_length_pos (message : UnderlyingTradingStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingTradingStatusMessage) (rest : List UInt8) :
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

end UnderlyingTradingStatusMessage

/-- Any Data, selected by Message Type -/
inductive Data where
  | systemTimeMessage (message : SystemTimeMessage) -- "1" 0x31
  | seriesUpdate (message : SeriesUpdate) -- "P" 0x50
  | complexStrategyDefinitionMessage (message : ComplexStrategyDefinitionMessage) -- "C" 0x43
  | systemStateMessage (message : SystemStateMessage) -- "S" 0x53
  | compactComplexTopOfMarketBidMessage (message : CompactComplexTopOfMarketBidMessage) -- "b" 0x62
  | compactComplexTopOfMarketOfferMessage (message : CompactComplexTopOfMarketOfferMessage) -- "o" 0x6F
  | wideComplexTopOfMarketBidMessage (message : WideComplexTopOfMarketBidMessage) -- "e" 0x65
  | wideComplexTopOfMarketOfferMessage (message : WideComplexTopOfMarketOfferMessage) -- "f" 0x66
  | compactComplexDoubleSidedTopOfMarketMessage (message : CompactComplexDoubleSidedTopOfMarketMessage) -- "m" 0x6D
  | wideComplexDoubleSidedTopOfMarketMessage (message : WideComplexDoubleSidedTopOfMarketMessage) -- "w" 0x77
  | strategyTradeMessage (message : StrategyTradeMessage) -- "t" 0x74
  | underlyingTradingStatusMessage (message : UnderlyingTradingStatusMessage) -- "H" 0x48
  deriving DecidableEq, Repr

namespace Data

/-- The Message Type each message is sent under -/
def tag : Data → BitVec 8
  | .systemTimeMessage _ => 49
  | .seriesUpdate _ => 80
  | .complexStrategyDefinitionMessage _ => 67
  | .systemStateMessage _ => 83
  | .compactComplexTopOfMarketBidMessage _ => 98
  | .compactComplexTopOfMarketOfferMessage _ => 111
  | .wideComplexTopOfMarketBidMessage _ => 101
  | .wideComplexTopOfMarketOfferMessage _ => 102
  | .compactComplexDoubleSidedTopOfMarketMessage _ => 109
  | .wideComplexDoubleSidedTopOfMarketMessage _ => 119
  | .strategyTradeMessage _ => 116
  | .underlyingTradingStatusMessage _ => 72

def encode : Data → List UInt8
  | .systemTimeMessage message => SystemTimeMessage.encode message
  | .seriesUpdate message => SeriesUpdate.encode message
  | .complexStrategyDefinitionMessage message => ComplexStrategyDefinitionMessage.encode message
  | .systemStateMessage message => SystemStateMessage.encode message
  | .compactComplexTopOfMarketBidMessage message => CompactComplexTopOfMarketBidMessage.encode message
  | .compactComplexTopOfMarketOfferMessage message => CompactComplexTopOfMarketOfferMessage.encode message
  | .wideComplexTopOfMarketBidMessage message => WideComplexTopOfMarketBidMessage.encode message
  | .wideComplexTopOfMarketOfferMessage message => WideComplexTopOfMarketOfferMessage.encode message
  | .compactComplexDoubleSidedTopOfMarketMessage message => CompactComplexDoubleSidedTopOfMarketMessage.encode message
  | .wideComplexDoubleSidedTopOfMarketMessage message => WideComplexDoubleSidedTopOfMarketMessage.encode message
  | .strategyTradeMessage message => StrategyTradeMessage.encode message
  | .underlyingTradingStatusMessage message => UnderlyingTradingStatusMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Data) : (encode message).length ≤ 3858 := by
  cases message with
  | systemTimeMessage inner =>
    simp only [encode, SystemTimeMessage.encode_length]
    omega
  | seriesUpdate inner =>
    simp only [encode, SeriesUpdate.encode_length]
    omega
  | complexStrategyDefinitionMessage inner =>
    have bound_inner := ComplexStrategyDefinitionMessage.encode_length_le inner
    simp only [encode]
    omega
  | systemStateMessage inner =>
    simp only [encode, SystemStateMessage.encode_length]
    omega
  | compactComplexTopOfMarketBidMessage inner =>
    simp only [encode, CompactComplexTopOfMarketBidMessage.encode_length]
    omega
  | compactComplexTopOfMarketOfferMessage inner =>
    simp only [encode, CompactComplexTopOfMarketOfferMessage.encode_length]
    omega
  | wideComplexTopOfMarketBidMessage inner =>
    simp only [encode, WideComplexTopOfMarketBidMessage.encode_length]
    omega
  | wideComplexTopOfMarketOfferMessage inner =>
    simp only [encode, WideComplexTopOfMarketOfferMessage.encode_length]
    omega
  | compactComplexDoubleSidedTopOfMarketMessage inner =>
    simp only [encode, CompactComplexDoubleSidedTopOfMarketMessage.encode_length]
    omega
  | wideComplexDoubleSidedTopOfMarketMessage inner =>
    simp only [encode, WideComplexDoubleSidedTopOfMarketMessage.encode_length]
    omega
  | strategyTradeMessage inner =>
    simp only [encode, StrategyTradeMessage.encode_length]
    omega
  | underlyingTradingStatusMessage inner =>
    simp only [encode, UnderlyingTradingStatusMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Data × List UInt8) :=
  if tag = 49 then (SystemTimeMessage.decode bytes).map fun (message, rest) => (.systemTimeMessage message, rest)
  else if tag = 80 then (SeriesUpdate.decode bytes).map fun (message, rest) => (.seriesUpdate message, rest)
  else if tag = 67 then (ComplexStrategyDefinitionMessage.decode bytes).map fun (message, rest) => (.complexStrategyDefinitionMessage message, rest)
  else if tag = 83 then (SystemStateMessage.decode bytes).map fun (message, rest) => (.systemStateMessage message, rest)
  else if tag = 98 then (CompactComplexTopOfMarketBidMessage.decode bytes).map fun (message, rest) => (.compactComplexTopOfMarketBidMessage message, rest)
  else if tag = 111 then (CompactComplexTopOfMarketOfferMessage.decode bytes).map fun (message, rest) => (.compactComplexTopOfMarketOfferMessage message, rest)
  else if tag = 101 then (WideComplexTopOfMarketBidMessage.decode bytes).map fun (message, rest) => (.wideComplexTopOfMarketBidMessage message, rest)
  else if tag = 102 then (WideComplexTopOfMarketOfferMessage.decode bytes).map fun (message, rest) => (.wideComplexTopOfMarketOfferMessage message, rest)
  else if tag = 109 then (CompactComplexDoubleSidedTopOfMarketMessage.decode bytes).map fun (message, rest) => (.compactComplexDoubleSidedTopOfMarketMessage message, rest)
  else if tag = 119 then (WideComplexDoubleSidedTopOfMarketMessage.decode bytes).map fun (message, rest) => (.wideComplexDoubleSidedTopOfMarketMessage message, rest)
  else if tag = 116 then (StrategyTradeMessage.decode bytes).map fun (message, rest) => (.strategyTradeMessage message, rest)
  else if tag = 72 then (UnderlyingTradingStatusMessage.decode bytes).map fun (message, rest) => (.underlyingTradingStatusMessage message, rest)
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
theorem encode_length_le (message : ApplicationMessage) : (encode message).length ≤ 3859 := by
  unfold encode
  cases message.data with
  | systemTimeMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SystemTimeMessage.encode_length]
    omega
  | seriesUpdate inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SeriesUpdate.encode_length]
    omega
  | complexStrategyDefinitionMessage inner =>
    have bound_inner := ComplexStrategyDefinitionMessage.encode_length_le inner
    simp only [Data.encode, List.length_append, encodeUInt_length]
    omega
  | systemStateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SystemStateMessage.encode_length]
    omega
  | compactComplexTopOfMarketBidMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, CompactComplexTopOfMarketBidMessage.encode_length]
    omega
  | compactComplexTopOfMarketOfferMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, CompactComplexTopOfMarketOfferMessage.encode_length]
    omega
  | wideComplexTopOfMarketBidMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, WideComplexTopOfMarketBidMessage.encode_length]
    omega
  | wideComplexTopOfMarketOfferMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, WideComplexTopOfMarketOfferMessage.encode_length]
    omega
  | compactComplexDoubleSidedTopOfMarketMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, CompactComplexDoubleSidedTopOfMarketMessage.encode_length]
    omega
  | wideComplexDoubleSidedTopOfMarketMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, WideComplexDoubleSidedTopOfMarketMessage.encode_length]
    omega
  | strategyTradeMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, StrategyTradeMessage.encode_length]
    omega
  | underlyingTradingStatusMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, UnderlyingTradingStatusMessage.encode_length]
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
theorem encode_length_le (message : Payload) : (encode message).length ≤ 3859 := by
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
  packetLength : BitVec 16
  sessionNumber : BitVec 8
  payload : Payload
  deriving DecidableEq, Repr

namespace MachMessage

def encode (message : MachMessage) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeUIntLE 2 message.packetLength
    ++ (encodeUIntLE 1 (Payload.tag message.payload)
    ++ (encodeUIntLE 1 message.sessionNumber
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (MachMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (packetLength, bytes) ← decodeUIntLE 2 bytes
  let (packetType, bytes) ← decodeUIntLE 1 bytes
  let (sessionNumber, bytes) ← decodeUIntLE 1 bytes
  let (payload, bytes) ← Payload.decode packetType bytes
  pure ({ sequenceNumber, packetLength, sessionNumber, payload }, bytes)

theorem encode_length_pos (message : MachMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MachMessage) : (encode message).length ≤ 3871 := by
  unfold encode
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

@[simp] theorem decode_encode (message : MachMessage) (rest : List UInt8) :
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
  rw [Payload.decode_encode, some_bind]
  rfl

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

end Omi.MiaxMiaxoptionsComplextopofmarketMachV11
