import Omi.Wire

/-!
# Miami International Holdings Top Of Market v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Application Message is not framed: its length Packet Length is not an integer it reads.

Note: Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxPearloptionsTopofmarketMachV10

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
  | positionClosingOrdersOnly -- Position Closing Orders Only
  | openAndClosePositions -- Open And Close Positions
  | unlisted (byte : { byte : UInt8 // byte ∉ RestrictedOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RestrictedOption

def toByte : RestrictedOption → UInt8
  | .positionClosingOrdersOnly => 0x59
  | .openAndClosePositions => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RestrictedOption :=
  if byte = 0x59 then .positionClosingOrdersOnly
  else .openAndClosePositions

def ofByte (byte : UInt8) : RestrictedOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RestrictedOption) : ofByte value.toByte = value := by
  cases value with
  | positionClosingOrdersOnly => decide
  | openAndClosePositions => decide
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
  | farMonth -- Far Month
  | nearMonth -- Near Month
  | unlisted (byte : { byte : UInt8 // byte ∉ LongTermOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LongTermOption

def toByte : LongTermOption → UInt8
  | .farMonth => 0x59
  | .nearMonth => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LongTermOption :=
  if byte = 0x59 then .farMonth
  else .nearMonth

def ofByte (byte : UInt8) : LongTermOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LongTermOption) : ofByte value.toByte = value := by
  cases value with
  | farMonth => decide
  | nearMonth => decide
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
  | activeTradable -- Active Tradable
  | inactiveNotTradable -- Inactive Not Tradable
  | unlisted (byte : { byte : UInt8 // byte ∉ ActiveOnPearl.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ActiveOnPearl

def toByte : ActiveOnPearl → UInt8
  | .activeTradable => 0x41
  | .inactiveNotTradable => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ActiveOnPearl :=
  if byte = 0x41 then .activeTradable
  else .inactiveNotTradable

def ofByte (byte : UInt8) : ActiveOnPearl :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ActiveOnPearl) : ofByte value.toByte = value := by
  cases value with
  | activeTradable => decide
  | inactiveNotTradable => decide
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
  | penny001 -- Penny 001
  | penny001_4e -- Penny 001
  | nickel005 -- Nickel 005
  | unlisted (byte : { byte : UInt8 // byte ∉ PearlBboPostingIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PearlBboPostingIncrementIndicator

def toByte : PearlBboPostingIncrementIndicator → UInt8
  | .penny001 => 0x50
  | .penny001_4e => 0x4E
  | .nickel005 => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PearlBboPostingIncrementIndicator :=
  if byte = 0x50 then .penny001
  else if byte = 0x4E then .penny001_4e
  else .nickel005

def ofByte (byte : UInt8) : PearlBboPostingIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PearlBboPostingIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny001 => decide
  | penny001_4e => decide
  | nickel005 => decide
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
  | penny001 -- Penny 001
  | penny001_4e -- Penny 001
  | nickel005 -- Nickel 005
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityAcceptanceIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityAcceptanceIncrementIndicator

def toByte : LiquidityAcceptanceIncrementIndicator → UInt8
  | .penny001 => 0x50
  | .penny001_4e => 0x4E
  | .nickel005 => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityAcceptanceIncrementIndicator :=
  if byte = 0x50 then .penny001
  else if byte = 0x4E then .penny001_4e
  else .nickel005

def ofByte (byte : UInt8) : LiquidityAcceptanceIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityAcceptanceIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny001 => decide
  | penny001_4e => decide
  | nickel005 => decide
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
  | nationalStock -- National Stock
  | finraAdf -- Finra Adf
  | marketIndependent -- Market Independent
  | internationalSecurities -- International Securities
  | edgaExchange -- Edga Exchange
  | edgxExchange -- Edgx Exchange
  | chicagoStock -- Chicago Stock
  | nyseEuronext -- Nyse Euronext
  | nyseArca -- Nyse Arca
  | nasdaqOmx -- Nasdaq Omx
  | nasdaqOmx_54 -- Nasdaq Omx
  | iex -- Iex
  | nasdaqOmxPhlx -- Nasdaq Omx Phlx
  | batsYExchange -- Bats Y Exchange
  | batsExchange -- Bats Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningUnderlyingMarketCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningUnderlyingMarketCode

def toByte : OpeningUnderlyingMarketCode → UInt8
  | .nyseAmex => 0x41
  | .nasdaqOmxBx => 0x42
  | .nationalStock => 0x43
  | .finraAdf => 0x44
  | .marketIndependent => 0x45
  | .internationalSecurities => 0x49
  | .edgaExchange => 0x4A
  | .edgxExchange => 0x4B
  | .chicagoStock => 0x4D
  | .nyseEuronext => 0x4E
  | .nyseArca => 0x50
  | .nasdaqOmx => 0x51
  | .nasdaqOmx_54 => 0x54
  | .iex => 0x56
  | .nasdaqOmxPhlx => 0x58
  | .batsYExchange => 0x59
  | .batsExchange => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningUnderlyingMarketCode :=
  if byte = 0x41 then .nyseAmex
  else if byte = 0x42 then .nasdaqOmxBx
  else if byte = 0x43 then .nationalStock
  else if byte = 0x44 then .finraAdf
  else if byte = 0x45 then .marketIndependent
  else if byte = 0x49 then .internationalSecurities
  else if byte = 0x4A then .edgaExchange
  else if byte = 0x4B then .edgxExchange
  else if byte = 0x4D then .chicagoStock
  else if byte = 0x4E then .nyseEuronext
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaqOmx
  else if byte = 0x54 then .nasdaqOmx_54
  else if byte = 0x56 then .iex
  else if byte = 0x58 then .nasdaqOmxPhlx
  else if byte = 0x59 then .batsYExchange
  else .batsExchange

def ofByte (byte : UInt8) : OpeningUnderlyingMarketCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningUnderlyingMarketCode) : ofByte value.toByte = value := by
  cases value with
  | nyseAmex => decide
  | nasdaqOmxBx => decide
  | nationalStock => decide
  | finraAdf => decide
  | marketIndependent => decide
  | internationalSecurities => decide
  | edgaExchange => decide
  | edgxExchange => decide
  | chicagoStock => decide
  | nyseEuronext => decide
  | nyseArca => decide
  | nasdaqOmx => decide
  | nasdaqOmx_54 => decide
  | iex => decide
  | nasdaqOmxPhlx => decide
  | batsYExchange => decide
  | batsExchange => decide
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
  | start -- Start
  | end_ -- End
  | start_31 -- Start
  | end__32 -- End
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemStatus

def toByte : SystemStatus → UInt8
  | .start => 0x53
  | .end_ => 0x43
  | .start_31 => 0x31
  | .end__32 => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemStatus :=
  if byte = 0x53 then .start
  else if byte = 0x43 then .end_
  else if byte = 0x31 then .start_31
  else .end__32

def ofByte (byte : UInt8) : SystemStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemStatus) : ofByte value.toByte = value := by
  cases value with
  | start => decide
  | end_ => decide
  | start_31 => decide
  | end__32 => decide
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
  | quoteContainsPublicCustomerInterest -- Quote Contains Public Customer Interest
  | quoteIsNotFirm -- Quote Is Not Firm
  | reservedForFutureUse -- Reserved For Future Use
  | tradingHalt -- Trading Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ PbboCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PbboCondition

def toByte : PbboCondition → UInt8
  | .regular => 0x41
  | .quoteContainsPublicCustomerInterest => 0x42
  | .quoteIsNotFirm => 0x43
  | .reservedForFutureUse => 0x52
  | .tradingHalt => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PbboCondition :=
  if byte = 0x41 then .regular
  else if byte = 0x42 then .quoteContainsPublicCustomerInterest
  else if byte = 0x43 then .quoteIsNotFirm
  else if byte = 0x52 then .reservedForFutureUse
  else .tradingHalt

def ofByte (byte : UInt8) : PbboCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PbboCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | quoteContainsPublicCustomerInterest => decide
  | quoteIsNotFirm => decide
  | reservedForFutureUse => decide
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
  | quoteContainsPublicCustomerInterest -- Quote Contains Public Customer Interest
  | quoteIsNotFirm -- Quote Is Not Firm
  | reservedForFutureUse -- Reserved For Future Use
  | tradingHalt -- Trading Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ BidCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BidCondition

def toByte : BidCondition → UInt8
  | .regular => 0x41
  | .quoteContainsPublicCustomerInterest => 0x42
  | .quoteIsNotFirm => 0x43
  | .reservedForFutureUse => 0x52
  | .tradingHalt => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BidCondition :=
  if byte = 0x41 then .regular
  else if byte = 0x42 then .quoteContainsPublicCustomerInterest
  else if byte = 0x43 then .quoteIsNotFirm
  else if byte = 0x52 then .reservedForFutureUse
  else .tradingHalt

def ofByte (byte : UInt8) : BidCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BidCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | quoteContainsPublicCustomerInterest => decide
  | quoteIsNotFirm => decide
  | reservedForFutureUse => decide
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
  | quoteContainsPublicCustomerInterest -- Quote Contains Public Customer Interest
  | quoteIsNotFirm -- Quote Is Not Firm
  | reservedForFutureUse -- Reserved For Future Use
  | tradingHalt -- Trading Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ OfferCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OfferCondition

def toByte : OfferCondition → UInt8
  | .regular => 0x41
  | .quoteContainsPublicCustomerInterest => 0x42
  | .quoteIsNotFirm => 0x43
  | .reservedForFutureUse => 0x52
  | .tradingHalt => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OfferCondition :=
  if byte = 0x41 then .regular
  else if byte = 0x42 then .quoteContainsPublicCustomerInterest
  else if byte = 0x43 then .quoteIsNotFirm
  else if byte = 0x52 then .reservedForFutureUse
  else .tradingHalt

def ofByte (byte : UInt8) : OfferCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OfferCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | quoteContainsPublicCustomerInterest => decide
  | quoteIsNotFirm => decide
  | reservedForFutureUse => decide
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
  | cancelOfTrade -- Cancel Of Trade
  | tradeThatIsLateAndIsOutOfSequence -- Trade That Is Late And Is Out Of Sequence
  | cancelOfTheLastReportedTrade -- Cancel Of The Last Reported Trade
  | tradeThatIsLateAndIsInCorrectSequence -- Trade That Is Late And Is In Correct Sequence
  | cancelOfTheFirstOpeningReportedTrade -- Cancel Of The First Opening Reported Trade
  | tradeThatIsLateReportOfTheOpeningTradeAndIsOutOfSequence -- Trade That Is Late Report Of The Opening Trade And Is Out Of Sequence
  | cancelOfTheOnlyReportedTrade -- Cancel Of The Only Reported Trade
  | tradeThatIsLateReportOfTheOpeningTradeAndIsInCorrectSequence -- Trade That Is Late Report Of The Opening Trade And Is In Correct Sequence
  | reservedForFutureUse -- Reserved For Future Use
  | tradeDueToReopeningOfAnOptionInWhichTradingHasBeenPreviouslyHalted -- Trade Due To Reopening Of An Option In Which Trading Has Been Previously Halted
  | reservedForFutureUse_4b -- Reserved For Future Use
  | reservedForFutureUse_4c -- Reserved For Future Use
  | reservedForFutureUse_4d -- Reserved For Future Use
  | reservedForFutureUse_4e -- Reserved For Future Use
  | reservedForFutureUse_4f -- Reserved For Future Use
  | reservedForFutureUse_50 -- Reserved For Future Use
  | reservedForFutureUse_51 -- Reserved For Future Use
  | tradeWasTheExecutionOfAnOrderWhichWasStoppedAtAPriceThatDidNotConstituteATradeThroughOnAnotherMarketAtTheTimeOfTheStop -- Trade Was The Execution Of An Order Which Was Stopped At A Price That Did Not Constitute A Trade Through On Another Market At The Time Of The Stop
  | tradeWasTheExecutionOfAnOrderIdentified -- Trade Was The Execution Of An Order Identified
  | reservedForFutureUse_54 -- Reserved For Future Use
  | tradeThatIsTradeThroughExempt -- Trade That Is Trade Through Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCondition

def toByte : TradeCondition → UInt8
  | .regular => 0x20
  | .cancelOfTrade => 0x41
  | .tradeThatIsLateAndIsOutOfSequence => 0x42
  | .cancelOfTheLastReportedTrade => 0x43
  | .tradeThatIsLateAndIsInCorrectSequence => 0x44
  | .cancelOfTheFirstOpeningReportedTrade => 0x45
  | .tradeThatIsLateReportOfTheOpeningTradeAndIsOutOfSequence => 0x46
  | .cancelOfTheOnlyReportedTrade => 0x47
  | .tradeThatIsLateReportOfTheOpeningTradeAndIsInCorrectSequence => 0x48
  | .reservedForFutureUse => 0x49
  | .tradeDueToReopeningOfAnOptionInWhichTradingHasBeenPreviouslyHalted => 0x4A
  | .reservedForFutureUse_4b => 0x4B
  | .reservedForFutureUse_4c => 0x4C
  | .reservedForFutureUse_4d => 0x4D
  | .reservedForFutureUse_4e => 0x4E
  | .reservedForFutureUse_4f => 0x4F
  | .reservedForFutureUse_50 => 0x50
  | .reservedForFutureUse_51 => 0x51
  | .tradeWasTheExecutionOfAnOrderWhichWasStoppedAtAPriceThatDidNotConstituteATradeThroughOnAnotherMarketAtTheTimeOfTheStop => 0x52
  | .tradeWasTheExecutionOfAnOrderIdentified => 0x53
  | .reservedForFutureUse_54 => 0x54
  | .tradeThatIsTradeThroughExempt => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCondition :=
  if byte = 0x20 then .regular
  else if byte = 0x41 then .cancelOfTrade
  else if byte = 0x42 then .tradeThatIsLateAndIsOutOfSequence
  else if byte = 0x43 then .cancelOfTheLastReportedTrade
  else if byte = 0x44 then .tradeThatIsLateAndIsInCorrectSequence
  else if byte = 0x45 then .cancelOfTheFirstOpeningReportedTrade
  else if byte = 0x46 then .tradeThatIsLateReportOfTheOpeningTradeAndIsOutOfSequence
  else if byte = 0x47 then .cancelOfTheOnlyReportedTrade
  else if byte = 0x48 then .tradeThatIsLateReportOfTheOpeningTradeAndIsInCorrectSequence
  else if byte = 0x49 then .reservedForFutureUse
  else if byte = 0x4A then .tradeDueToReopeningOfAnOptionInWhichTradingHasBeenPreviouslyHalted
  else if byte = 0x4B then .reservedForFutureUse_4b
  else if byte = 0x4C then .reservedForFutureUse_4c
  else if byte = 0x4D then .reservedForFutureUse_4d
  else if byte = 0x4E then .reservedForFutureUse_4e
  else if byte = 0x4F then .reservedForFutureUse_4f
  else if byte = 0x50 then .reservedForFutureUse_50
  else if byte = 0x51 then .reservedForFutureUse_51
  else if byte = 0x52 then .tradeWasTheExecutionOfAnOrderWhichWasStoppedAtAPriceThatDidNotConstituteATradeThroughOnAnotherMarketAtTheTimeOfTheStop
  else if byte = 0x53 then .tradeWasTheExecutionOfAnOrderIdentified
  else if byte = 0x54 then .reservedForFutureUse_54
  else .tradeThatIsTradeThroughExempt

def ofByte (byte : UInt8) : TradeCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | cancelOfTrade => decide
  | tradeThatIsLateAndIsOutOfSequence => decide
  | cancelOfTheLastReportedTrade => decide
  | tradeThatIsLateAndIsInCorrectSequence => decide
  | cancelOfTheFirstOpeningReportedTrade => decide
  | tradeThatIsLateReportOfTheOpeningTradeAndIsOutOfSequence => decide
  | cancelOfTheOnlyReportedTrade => decide
  | tradeThatIsLateReportOfTheOpeningTradeAndIsInCorrectSequence => decide
  | reservedForFutureUse => decide
  | tradeDueToReopeningOfAnOptionInWhichTradingHasBeenPreviouslyHalted => decide
  | reservedForFutureUse_4b => decide
  | reservedForFutureUse_4c => decide
  | reservedForFutureUse_4d => decide
  | reservedForFutureUse_4e => decide
  | reservedForFutureUse_4f => decide
  | reservedForFutureUse_50 => decide
  | reservedForFutureUse_51 => decide
  | tradeWasTheExecutionOfAnOrderWhichWasStoppedAtAPriceThatDidNotConstituteATradeThroughOnAnotherMarketAtTheTimeOfTheStop => decide
  | tradeWasTheExecutionOfAnOrderIdentified => decide
  | reservedForFutureUse_54 => decide
  | tradeThatIsTradeThroughExempt => decide
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

/-- Event Reason: one byte code -/
def EventReason.codes : List UInt8 :=
  [0x41, 0x4D]

inductive EventReason where
  | resultedFromAutomaticmarketDrivenEvent -- Resulted From Automaticmarket Driven Event
  | manuallyInitiated -- Manually Initiated
  | unlisted (byte : { byte : UInt8 // byte ∉ EventReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventReason

def toByte : EventReason → UInt8
  | .resultedFromAutomaticmarketDrivenEvent => 0x41
  | .manuallyInitiated => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventReason :=
  if byte = 0x41 then .resultedFromAutomaticmarketDrivenEvent
  else .manuallyInitiated

def ofByte (byte : UInt8) : EventReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventReason) : ofByte value.toByte = value := by
  cases value with
  | resultedFromAutomaticmarketDrivenEvent => decide
  | manuallyInitiated => decide
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

/-- Compact Top Of Market Bid Message: 15 bytes -/
structure CompactTopOfMarketBidMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  pbboPrice : BitVec 16
  pbboSize : BitVec 16
  pbboPriorityCustomerSize : BitVec 16
  pbboCondition : PbboCondition
  deriving DecidableEq, Repr

namespace CompactTopOfMarketBidMessage

def encode (message : CompactTopOfMarketBidMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.pbboPrice
    ++ (encodeUIntLE 2 message.pbboSize
    ++ (encodeUIntLE 2 message.pbboPriorityCustomerSize
    ++ (PbboCondition.encode message.pbboCondition)))))

def decode (bytes : List UInt8) : Option (CompactTopOfMarketBidMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (pbboPrice, bytes) ← decodeUIntLE 2 bytes
  let (pbboSize, bytes) ← decodeUIntLE 2 bytes
  let (pbboPriorityCustomerSize, bytes) ← decodeUIntLE 2 bytes
  let (pbboCondition, bytes) ← PbboCondition.decode bytes
  pure ({ nanoseconds, productId, pbboPrice, pbboSize, pbboPriorityCustomerSize, pbboCondition }, bytes)

@[simp] theorem encode_length (message : CompactTopOfMarketBidMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PbboCondition.encode_length]

theorem encode_length_pos (message : CompactTopOfMarketBidMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CompactTopOfMarketBidMessage) (rest : List UInt8) :
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

end CompactTopOfMarketBidMessage

/-- Compact Top Of Market Best Offer Message: 15 bytes -/
structure CompactTopOfMarketBestOfferMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  pbboPrice : BitVec 16
  pbboSize : BitVec 16
  pbboPriorityCustomerSize : BitVec 16
  pbboCondition : PbboCondition
  deriving DecidableEq, Repr

namespace CompactTopOfMarketBestOfferMessage

def encode (message : CompactTopOfMarketBestOfferMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.pbboPrice
    ++ (encodeUIntLE 2 message.pbboSize
    ++ (encodeUIntLE 2 message.pbboPriorityCustomerSize
    ++ (PbboCondition.encode message.pbboCondition)))))

def decode (bytes : List UInt8) : Option (CompactTopOfMarketBestOfferMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (pbboPrice, bytes) ← decodeUIntLE 2 bytes
  let (pbboSize, bytes) ← decodeUIntLE 2 bytes
  let (pbboPriorityCustomerSize, bytes) ← decodeUIntLE 2 bytes
  let (pbboCondition, bytes) ← PbboCondition.decode bytes
  pure ({ nanoseconds, productId, pbboPrice, pbboSize, pbboPriorityCustomerSize, pbboCondition }, bytes)

@[simp] theorem encode_length (message : CompactTopOfMarketBestOfferMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PbboCondition.encode_length]

theorem encode_length_pos (message : CompactTopOfMarketBestOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CompactTopOfMarketBestOfferMessage) (rest : List UInt8) :
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

end CompactTopOfMarketBestOfferMessage

/-- Wide Top Of Market Best Bid Message: 21 bytes -/
structure WideTopOfMarketBestBidMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  widePbboPrice : BitVec 32
  widePbboSize : BitVec 32
  widePbboPriorityCustomerSize : BitVec 32
  pbboCondition : PbboCondition
  deriving DecidableEq, Repr

namespace WideTopOfMarketBestBidMessage

def encode (message : WideTopOfMarketBestBidMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.widePbboPrice
    ++ (encodeUIntLE 4 message.widePbboSize
    ++ (encodeUIntLE 4 message.widePbboPriorityCustomerSize
    ++ (PbboCondition.encode message.pbboCondition)))))

def decode (bytes : List UInt8) : Option (WideTopOfMarketBestBidMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (widePbboPrice, bytes) ← decodeUIntLE 4 bytes
  let (widePbboSize, bytes) ← decodeUIntLE 4 bytes
  let (widePbboPriorityCustomerSize, bytes) ← decodeUIntLE 4 bytes
  let (pbboCondition, bytes) ← PbboCondition.decode bytes
  pure ({ nanoseconds, productId, widePbboPrice, widePbboSize, widePbboPriorityCustomerSize, pbboCondition }, bytes)

@[simp] theorem encode_length (message : WideTopOfMarketBestBidMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PbboCondition.encode_length]

theorem encode_length_pos (message : WideTopOfMarketBestBidMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WideTopOfMarketBestBidMessage) (rest : List UInt8) :
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

end WideTopOfMarketBestBidMessage

/-- Wide Top Of Market Best Offer Message: 21 bytes -/
structure WideTopOfMarketBestOfferMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  widePbboPrice : BitVec 32
  widePbboSize : BitVec 32
  widePbboPriorityCustomerSize : BitVec 32
  pbboCondition : PbboCondition
  deriving DecidableEq, Repr

namespace WideTopOfMarketBestOfferMessage

def encode (message : WideTopOfMarketBestOfferMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.widePbboPrice
    ++ (encodeUIntLE 4 message.widePbboSize
    ++ (encodeUIntLE 4 message.widePbboPriorityCustomerSize
    ++ (PbboCondition.encode message.pbboCondition)))))

def decode (bytes : List UInt8) : Option (WideTopOfMarketBestOfferMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (widePbboPrice, bytes) ← decodeUIntLE 4 bytes
  let (widePbboSize, bytes) ← decodeUIntLE 4 bytes
  let (widePbboPriorityCustomerSize, bytes) ← decodeUIntLE 4 bytes
  let (pbboCondition, bytes) ← PbboCondition.decode bytes
  pure ({ nanoseconds, productId, widePbboPrice, widePbboSize, widePbboPriorityCustomerSize, pbboCondition }, bytes)

@[simp] theorem encode_length (message : WideTopOfMarketBestOfferMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PbboCondition.encode_length]

theorem encode_length_pos (message : WideTopOfMarketBestOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WideTopOfMarketBestOfferMessage) (rest : List UInt8) :
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

end WideTopOfMarketBestOfferMessage

/-- Compact Double Sided Top Of Market Message: 22 bytes -/
structure CompactDoubleSidedTopOfMarketMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  bidPrice : BitVec 16
  bidSize : BitVec 16
  bidPriorityCustomerSize : BitVec 16
  bidCondition : BidCondition
  offerPrice : BitVec 16
  offerSize : BitVec 16
  offerPriorityCustomerSize : BitVec 16
  offerCondition : OfferCondition
  deriving DecidableEq, Repr

namespace CompactDoubleSidedTopOfMarketMessage

def encode (message : CompactDoubleSidedTopOfMarketMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.bidPrice
    ++ (encodeUIntLE 2 message.bidSize
    ++ (encodeUIntLE 2 message.bidPriorityCustomerSize
    ++ (BidCondition.encode message.bidCondition
    ++ (encodeUIntLE 2 message.offerPrice
    ++ (encodeUIntLE 2 message.offerSize
    ++ (encodeUIntLE 2 message.offerPriorityCustomerSize
    ++ (OfferCondition.encode message.offerCondition)))))))))

def decode (bytes : List UInt8) : Option (CompactDoubleSidedTopOfMarketMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 2 bytes
  let (bidSize, bytes) ← decodeUIntLE 2 bytes
  let (bidPriorityCustomerSize, bytes) ← decodeUIntLE 2 bytes
  let (bidCondition, bytes) ← BidCondition.decode bytes
  let (offerPrice, bytes) ← decodeUIntLE 2 bytes
  let (offerSize, bytes) ← decodeUIntLE 2 bytes
  let (offerPriorityCustomerSize, bytes) ← decodeUIntLE 2 bytes
  let (offerCondition, bytes) ← OfferCondition.decode bytes
  pure ({ nanoseconds, productId, bidPrice, bidSize, bidPriorityCustomerSize, bidCondition, offerPrice, offerSize, offerPriorityCustomerSize, offerCondition }, bytes)

@[simp] theorem encode_length (message : CompactDoubleSidedTopOfMarketMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, BidCondition.encode_length, OfferCondition.encode_length]

theorem encode_length_pos (message : CompactDoubleSidedTopOfMarketMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CompactDoubleSidedTopOfMarketMessage) (rest : List UInt8) :
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

end CompactDoubleSidedTopOfMarketMessage

/-- Wide Double Sided Top Of Market Message: 34 bytes -/
structure WideDoubleSidedTopOfMarketMessage where
  nanoseconds : BitVec 32
  productId : BitVec 32
  wideBidPrice : BitVec 32
  wideBidSize : BitVec 32
  wideBidPriorityCustomerSize : BitVec 32
  bidCondition : BidCondition
  wideOfferPrice : BitVec 32
  wideOfferSize : BitVec 32
  wideOfferPriorityCustomerSize : BitVec 32
  offerCondition : OfferCondition
  deriving DecidableEq, Repr

namespace WideDoubleSidedTopOfMarketMessage

def encode (message : WideDoubleSidedTopOfMarketMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.wideBidPrice
    ++ (encodeUIntLE 4 message.wideBidSize
    ++ (encodeUIntLE 4 message.wideBidPriorityCustomerSize
    ++ (BidCondition.encode message.bidCondition
    ++ (encodeUIntLE 4 message.wideOfferPrice
    ++ (encodeUIntLE 4 message.wideOfferSize
    ++ (encodeUIntLE 4 message.wideOfferPriorityCustomerSize
    ++ (OfferCondition.encode message.offerCondition)))))))))

def decode (bytes : List UInt8) : Option (WideDoubleSidedTopOfMarketMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (wideBidPrice, bytes) ← decodeUIntLE 4 bytes
  let (wideBidSize, bytes) ← decodeUIntLE 4 bytes
  let (wideBidPriorityCustomerSize, bytes) ← decodeUIntLE 4 bytes
  let (bidCondition, bytes) ← BidCondition.decode bytes
  let (wideOfferPrice, bytes) ← decodeUIntLE 4 bytes
  let (wideOfferSize, bytes) ← decodeUIntLE 4 bytes
  let (wideOfferPriorityCustomerSize, bytes) ← decodeUIntLE 4 bytes
  let (offerCondition, bytes) ← OfferCondition.decode bytes
  pure ({ nanoseconds, productId, wideBidPrice, wideBidSize, wideBidPriorityCustomerSize, bidCondition, wideOfferPrice, wideOfferSize, wideOfferPriorityCustomerSize, offerCondition }, bytes)

@[simp] theorem encode_length (message : WideDoubleSidedTopOfMarketMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, BidCondition.encode_length, OfferCondition.encode_length]

theorem encode_length_pos (message : WideDoubleSidedTopOfMarketMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WideDoubleSidedTopOfMarketMessage) (rest : List UInt8) :
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

end WideDoubleSidedTopOfMarketMessage

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

/-- Underlying Trading Status Notification: 25 bytes -/
structure UnderlyingTradingStatusNotification where
  nanoseconds : BitVec 32
  underlyingSymbol : Alpha 11
  tradingStatus : Alpha 1
  eventReason : EventReason
  expectedEventTimeSecondsPart : BitVec 32
  expectedEventTimeNanoSecondsPart : BitVec 32
  deriving DecidableEq, Repr

namespace UnderlyingTradingStatusNotification

def encode (message : UnderlyingTradingStatusNotification) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.tradingStatus
    ++ (EventReason.encode message.eventReason
    ++ (encodeUIntLE 4 message.expectedEventTimeSecondsPart
    ++ (encodeUIntLE 4 message.expectedEventTimeNanoSecondsPart)))))

def decode (bytes : List UInt8) : Option (UnderlyingTradingStatusNotification × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (tradingStatus, bytes) ← Alpha.decode 1 bytes
  let (eventReason, bytes) ← EventReason.decode bytes
  let (expectedEventTimeSecondsPart, bytes) ← decodeUIntLE 4 bytes
  let (expectedEventTimeNanoSecondsPart, bytes) ← decodeUIntLE 4 bytes
  pure ({ nanoseconds, underlyingSymbol, tradingStatus, eventReason, expectedEventTimeSecondsPart, expectedEventTimeNanoSecondsPart }, bytes)

@[simp] theorem encode_length (message : UnderlyingTradingStatusNotification) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, EventReason.encode_length]

theorem encode_length_pos (message : UnderlyingTradingStatusNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingTradingStatusNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end UnderlyingTradingStatusNotification

/-- Any Data, selected by Message Type -/
inductive Data where
  | systemTimeMessage (message : SystemTimeMessage) -- "1" 0x31
  | seriesUpdateMessage (message : SeriesUpdateMessage) -- "P" 0x50
  | systemStateMessage (message : SystemStateMessage) -- "S" 0x53
  | compactTopOfMarketBidMessage (message : CompactTopOfMarketBidMessage) -- "B" 0x42
  | compactTopOfMarketBestOfferMessage (message : CompactTopOfMarketBestOfferMessage) -- "O" 0x4F
  | wideTopOfMarketBestBidMessage (message : WideTopOfMarketBestBidMessage) -- "W" 0x57
  | wideTopOfMarketBestOfferMessage (message : WideTopOfMarketBestOfferMessage) -- "A" 0x41
  | compactDoubleSidedTopOfMarketMessage (message : CompactDoubleSidedTopOfMarketMessage) -- "d" 0x64
  | wideDoubleSidedTopOfMarketMessage (message : WideDoubleSidedTopOfMarketMessage) -- "D" 0x44
  | lastSaleMessage (message : LastSaleMessage) -- "T" 0x54
  | tradeCancelMessage (message : TradeCancelMessage) -- "X" 0x58
  | underlyingTradingStatusNotification (message : UnderlyingTradingStatusNotification) -- "H" 0x48
  deriving DecidableEq, Repr

namespace Data

/-- The Message Type each message is sent under -/
def tag : Data → BitVec 8
  | .systemTimeMessage _ => 49
  | .seriesUpdateMessage _ => 80
  | .systemStateMessage _ => 83
  | .compactTopOfMarketBidMessage _ => 66
  | .compactTopOfMarketBestOfferMessage _ => 79
  | .wideTopOfMarketBestBidMessage _ => 87
  | .wideTopOfMarketBestOfferMessage _ => 65
  | .compactDoubleSidedTopOfMarketMessage _ => 100
  | .wideDoubleSidedTopOfMarketMessage _ => 68
  | .lastSaleMessage _ => 84
  | .tradeCancelMessage _ => 88
  | .underlyingTradingStatusNotification _ => 72

def encode : Data → List UInt8
  | .systemTimeMessage message => SystemTimeMessage.encode message
  | .seriesUpdateMessage message => SeriesUpdateMessage.encode message
  | .systemStateMessage message => SystemStateMessage.encode message
  | .compactTopOfMarketBidMessage message => CompactTopOfMarketBidMessage.encode message
  | .compactTopOfMarketBestOfferMessage message => CompactTopOfMarketBestOfferMessage.encode message
  | .wideTopOfMarketBestBidMessage message => WideTopOfMarketBestBidMessage.encode message
  | .wideTopOfMarketBestOfferMessage message => WideTopOfMarketBestOfferMessage.encode message
  | .compactDoubleSidedTopOfMarketMessage message => CompactDoubleSidedTopOfMarketMessage.encode message
  | .wideDoubleSidedTopOfMarketMessage message => WideDoubleSidedTopOfMarketMessage.encode message
  | .lastSaleMessage message => LastSaleMessage.encode message
  | .tradeCancelMessage message => TradeCancelMessage.encode message
  | .underlyingTradingStatusNotification message => UnderlyingTradingStatusNotification.encode message

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
  | compactTopOfMarketBidMessage inner =>
    simp only [encode, CompactTopOfMarketBidMessage.encode_length]
    omega
  | compactTopOfMarketBestOfferMessage inner =>
    simp only [encode, CompactTopOfMarketBestOfferMessage.encode_length]
    omega
  | wideTopOfMarketBestBidMessage inner =>
    simp only [encode, WideTopOfMarketBestBidMessage.encode_length]
    omega
  | wideTopOfMarketBestOfferMessage inner =>
    simp only [encode, WideTopOfMarketBestOfferMessage.encode_length]
    omega
  | compactDoubleSidedTopOfMarketMessage inner =>
    simp only [encode, CompactDoubleSidedTopOfMarketMessage.encode_length]
    omega
  | wideDoubleSidedTopOfMarketMessage inner =>
    simp only [encode, WideDoubleSidedTopOfMarketMessage.encode_length]
    omega
  | lastSaleMessage inner =>
    simp only [encode, LastSaleMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [encode, TradeCancelMessage.encode_length]
    omega
  | underlyingTradingStatusNotification inner =>
    simp only [encode, UnderlyingTradingStatusNotification.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Data × List UInt8) :=
  if tag = 49 then (SystemTimeMessage.decode bytes).map fun (message, rest) => (.systemTimeMessage message, rest)
  else if tag = 80 then (SeriesUpdateMessage.decode bytes).map fun (message, rest) => (.seriesUpdateMessage message, rest)
  else if tag = 83 then (SystemStateMessage.decode bytes).map fun (message, rest) => (.systemStateMessage message, rest)
  else if tag = 66 then (CompactTopOfMarketBidMessage.decode bytes).map fun (message, rest) => (.compactTopOfMarketBidMessage message, rest)
  else if tag = 79 then (CompactTopOfMarketBestOfferMessage.decode bytes).map fun (message, rest) => (.compactTopOfMarketBestOfferMessage message, rest)
  else if tag = 87 then (WideTopOfMarketBestBidMessage.decode bytes).map fun (message, rest) => (.wideTopOfMarketBestBidMessage message, rest)
  else if tag = 65 then (WideTopOfMarketBestOfferMessage.decode bytes).map fun (message, rest) => (.wideTopOfMarketBestOfferMessage message, rest)
  else if tag = 100 then (CompactDoubleSidedTopOfMarketMessage.decode bytes).map fun (message, rest) => (.compactDoubleSidedTopOfMarketMessage message, rest)
  else if tag = 68 then (WideDoubleSidedTopOfMarketMessage.decode bytes).map fun (message, rest) => (.wideDoubleSidedTopOfMarketMessage message, rest)
  else if tag = 84 then (LastSaleMessage.decode bytes).map fun (message, rest) => (.lastSaleMessage message, rest)
  else if tag = 88 then (TradeCancelMessage.decode bytes).map fun (message, rest) => (.tradeCancelMessage message, rest)
  else if tag = 72 then (UnderlyingTradingStatusNotification.decode bytes).map fun (message, rest) => (.underlyingTradingStatusNotification message, rest)
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
  | compactTopOfMarketBidMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, CompactTopOfMarketBidMessage.encode_length]
    omega
  | compactTopOfMarketBestOfferMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, CompactTopOfMarketBestOfferMessage.encode_length]
    omega
  | wideTopOfMarketBestBidMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, WideTopOfMarketBestBidMessage.encode_length]
    omega
  | wideTopOfMarketBestOfferMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, WideTopOfMarketBestOfferMessage.encode_length]
    omega
  | compactDoubleSidedTopOfMarketMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, CompactDoubleSidedTopOfMarketMessage.encode_length]
    omega
  | wideDoubleSidedTopOfMarketMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, WideDoubleSidedTopOfMarketMessage.encode_length]
    omega
  | lastSaleMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, LastSaleMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TradeCancelMessage.encode_length]
    omega
  | underlyingTradingStatusNotification inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, UnderlyingTradingStatusNotification.encode_length]
    omega

@[simp] theorem decode_encode (message : ApplicationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Data.decode_encode, some_bind]
  rfl

end ApplicationMessage

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

/-- Any Payload, selected by Packet Type -/
inductive Payload where
  | applicationMessage (message : ApplicationMessage) -- 3
  | heartbeat (message : Heartbeat) -- 0
  | startOfSession (message : StartOfSession) -- 1
  | endOfSession (message : EndOfSession) -- 2
  deriving DecidableEq, Repr

namespace Payload

/-- The Packet Type each message is sent under -/
def tag : Payload → BitVec 8
  | .applicationMessage _ => 3
  | .heartbeat _ => 0
  | .startOfSession _ => 1
  | .endOfSession _ => 2

def encode : Payload → List UInt8
  | .applicationMessage message => ApplicationMessage.encode message
  | .heartbeat message => Heartbeat.encode message
  | .startOfSession message => StartOfSession.encode message
  | .endOfSession message => EndOfSession.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 73 := by
  cases message with
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [encode]
    omega
  | heartbeat inner =>
    simp only [encode, Heartbeat.encode_length]
    omega
  | startOfSession inner =>
    simp only [encode, StartOfSession.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 3 then (ApplicationMessage.decode bytes).map fun (message, rest) => (.applicationMessage message, rest)
  else if tag = 0 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 1 then (StartOfSession.decode bytes).map fun (message, rest) => (.startOfSession message, rest)
  else if tag = 2 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
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
theorem encode_length_le (message : MachMessage) : (encode message).length ≤ 85 := by
  unfold encode
  cases message.payload with
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | heartbeat inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Heartbeat.encode_length]
    omega
  | startOfSession inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, StartOfSession.encode_length]
    omega
  | endOfSession inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EndOfSession.encode_length]
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

end Omi.MiaxPearloptionsTopofmarketMachV10
