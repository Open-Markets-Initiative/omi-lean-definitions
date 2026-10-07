import Wire

/-!
# New York Stock Exchange Best Quote And Trade v2.4.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Retail Pricing Indicator is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseAmexequitiesBqtXdpV24A

/-- Exchange Code: one byte code -/
def ExchangeCode.codes : List UInt8 :=
  [0x41, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x56, 0x5A]

inductive ExchangeCode where
  | nyseAmerican -- Nyse American
  | ltse -- Ltse
  | nyseTexas -- Nyse Texas
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | iex -- Iex
  | cboe -- Cboe
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeCode

def toByte : ExchangeCode → UInt8
  | .nyseAmerican => 0x41
  | .ltse => 0x4C
  | .nyseTexas => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .iex => 0x56
  | .cboe => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExchangeCode :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x56 then .iex
  else .cboe

def ofByte (byte : UInt8) : ExchangeCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeCode) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | ltse => decide
  | nyseTexas => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | iex => decide
  | cboe => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExchangeCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExchangeCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExchangeCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExchangeCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExchangeCode

/-- Security Type: one byte code -/
def SecurityType.codes : List UInt8 :=
  [0x41, 0x43, 0x44, 0x45, 0x46, 0x48, 0x49, 0x4C, 0x4D, 0x4F, 0x50, 0x52, 0x53, 0x54, 0x55, 0x57]

inductive SecurityType where
  | adr -- Adr
  | commonStock -- Common Stock
  | debentures -- Debentures
  | etf -- Etf
  | foreign -- Foreign
  | usDepositaryShares -- Us Depositary Shares
  | units -- Units
  | indexLinkedNotes -- Index Linked Notes
  | miscliquidTrust -- Miscliquid Trust
  | ordinaryShares -- Ordinary Shares
  | preferredStock -- Preferred Stock
  | rights -- Rights
  | sharesOfBeneficiaryInterest -- Shares Of Beneficiary Interest
  | test -- Test
  | closedEndFund -- Closed End Fund
  | warrant -- Warrant
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityType

def toByte : SecurityType → UInt8
  | .adr => 0x41
  | .commonStock => 0x43
  | .debentures => 0x44
  | .etf => 0x45
  | .foreign => 0x46
  | .usDepositaryShares => 0x48
  | .units => 0x49
  | .indexLinkedNotes => 0x4C
  | .miscliquidTrust => 0x4D
  | .ordinaryShares => 0x4F
  | .preferredStock => 0x50
  | .rights => 0x52
  | .sharesOfBeneficiaryInterest => 0x53
  | .test => 0x54
  | .closedEndFund => 0x55
  | .warrant => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityType :=
  if byte = 0x41 then .adr
  else if byte = 0x43 then .commonStock
  else if byte = 0x44 then .debentures
  else if byte = 0x45 then .etf
  else if byte = 0x46 then .foreign
  else if byte = 0x48 then .usDepositaryShares
  else if byte = 0x49 then .units
  else if byte = 0x4C then .indexLinkedNotes
  else if byte = 0x4D then .miscliquidTrust
  else if byte = 0x4F then .ordinaryShares
  else if byte = 0x50 then .preferredStock
  else if byte = 0x52 then .rights
  else if byte = 0x53 then .sharesOfBeneficiaryInterest
  else if byte = 0x54 then .test
  else if byte = 0x55 then .closedEndFund
  else .warrant

def ofByte (byte : UInt8) : SecurityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityType) : ofByte value.toByte = value := by
  cases value with
  | adr => decide
  | commonStock => decide
  | debentures => decide
  | etf => decide
  | foreign => decide
  | usDepositaryShares => decide
  | units => decide
  | indexLinkedNotes => decide
  | miscliquidTrust => decide
  | ordinaryShares => decide
  | preferredStock => decide
  | rights => decide
  | sharesOfBeneficiaryInterest => decide
  | test => decide
  | closedEndFund => decide
  | warrant => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityType

/-- Round Lot: one byte code -/
def RoundLot.codes : List UInt8 :=
  [0x59, 0x4E]

inductive RoundLot where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ RoundLot.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RoundLot

def toByte : RoundLot → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RoundLot :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : RoundLot :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RoundLot) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RoundLot) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RoundLot × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RoundLot) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RoundLot) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RoundLot

/-- Security Status: one byte code -/
def SecurityStatus.codes : List UInt8 :=
  [0x34, 0x35, 0x36, 0x41, 0x43, 0x44, 0x50, 0x42, 0x45, 0x4F, 0x4C, 0x58, 0x49, 0x47]

inductive SecurityStatus where
  | tradingHalt -- Trading Halt
  | resume -- Resume
  | suspend -- Suspend
  | shortSaleRestrictionActivatedDay1 -- Short Sale Restriction Activated Day 1
  | shortSaleRestrictionContinuedDay2 -- Short Sale Restriction Continued Day 2
  | shortSaleRestrictionDeactivated -- Short Sale Restriction Deactivated
  | preopening -- Preopening
  | beginAcceptingOrders -- Begin Accepting Orders
  | earlySession -- Early Session
  | coreSession -- Core Session
  | lateSessionNonNyseOnly -- Late Session Non Nyse Only
  | closed -- Closed
  | haltResumePriceIndication -- Halt Resume Price Indication
  | preOpeningPriceIndication -- Pre Opening Price Indication
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatus

def toByte : SecurityStatus → UInt8
  | .tradingHalt => 0x34
  | .resume => 0x35
  | .suspend => 0x36
  | .shortSaleRestrictionActivatedDay1 => 0x41
  | .shortSaleRestrictionContinuedDay2 => 0x43
  | .shortSaleRestrictionDeactivated => 0x44
  | .preopening => 0x50
  | .beginAcceptingOrders => 0x42
  | .earlySession => 0x45
  | .coreSession => 0x4F
  | .lateSessionNonNyseOnly => 0x4C
  | .closed => 0x58
  | .haltResumePriceIndication => 0x49
  | .preOpeningPriceIndication => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x34 then .tradingHalt
  else if byte = 0x35 then .resume
  else if byte = 0x36 then .suspend
  else if byte = 0x41 then .shortSaleRestrictionActivatedDay1
  else if byte = 0x43 then .shortSaleRestrictionContinuedDay2
  else if byte = 0x44 then .shortSaleRestrictionDeactivated
  else if byte = 0x50 then .preopening
  else if byte = 0x42 then .beginAcceptingOrders
  else if byte = 0x45 then .earlySession
  else if byte = 0x4F then .coreSession
  else if byte = 0x4C then .lateSessionNonNyseOnly
  else if byte = 0x58 then .closed
  else if byte = 0x49 then .haltResumePriceIndication
  else .preOpeningPriceIndication

def ofByte (byte : UInt8) : SecurityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatus) : ofByte value.toByte = value := by
  cases value with
  | tradingHalt => decide
  | resume => decide
  | suspend => decide
  | shortSaleRestrictionActivatedDay1 => decide
  | shortSaleRestrictionContinuedDay2 => decide
  | shortSaleRestrictionDeactivated => decide
  | preopening => decide
  | beginAcceptingOrders => decide
  | earlySession => decide
  | coreSession => decide
  | lateSessionNonNyseOnly => decide
  | closed => decide
  | haltResumePriceIndication => decide
  | preOpeningPriceIndication => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityStatus

/-- Halt Condition: one byte code -/
def HaltCondition.codes : List UInt8 :=
  [0x7E, 0x44, 0x49, 0x50, 0x4D, 0x58, 0x41, 0x43, 0x45, 0x46, 0x4E, 0x4F, 0x56, 0x36, 0x31, 0x32, 0x33]

inductive HaltCondition where
  | securityNotDelayedhalted -- Security Not Delayedhalted
  | newsReleasedNewsDissemination -- News Released News Dissemination
  | orderImbalance -- Order Imbalance
  | newsPending -- News Pending
  | luldPause -- Luld Pause
  | equipmentChangeover -- Equipment Changeover
  | additionalInformationRequested -- Additional Information Requested
  | regulatoryConcern -- Regulatory Concern
  | mergerEffective -- Merger Effective
  | etfComponentPricesNotAvailable -- Etf Component Prices Not Available
  | corporateAction -- Corporate Action
  | newSecurityOffering -- New Security Offering
  | intradayIndicativeValueNotAvailable -- Intraday Indicative Value Not Available
  | suspend -- Suspend
  | marketWideCircuitBreakerHaltLevel1 -- Market Wide Circuit Breaker Halt Level 1
  | marketWideCircuitBreakerHaltLevel2 -- Market Wide Circuit Breaker Halt Level 2
  | marketWideCircuitBreakerHaltLevel3 -- Market Wide Circuit Breaker Halt Level 3
  | unlisted (byte : { byte : UInt8 // byte ∉ HaltCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HaltCondition

def toByte : HaltCondition → UInt8
  | .securityNotDelayedhalted => 0x7E
  | .newsReleasedNewsDissemination => 0x44
  | .orderImbalance => 0x49
  | .newsPending => 0x50
  | .luldPause => 0x4D
  | .equipmentChangeover => 0x58
  | .additionalInformationRequested => 0x41
  | .regulatoryConcern => 0x43
  | .mergerEffective => 0x45
  | .etfComponentPricesNotAvailable => 0x46
  | .corporateAction => 0x4E
  | .newSecurityOffering => 0x4F
  | .intradayIndicativeValueNotAvailable => 0x56
  | .suspend => 0x36
  | .marketWideCircuitBreakerHaltLevel1 => 0x31
  | .marketWideCircuitBreakerHaltLevel2 => 0x32
  | .marketWideCircuitBreakerHaltLevel3 => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HaltCondition :=
  if byte = 0x7E then .securityNotDelayedhalted
  else if byte = 0x44 then .newsReleasedNewsDissemination
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x50 then .newsPending
  else if byte = 0x4D then .luldPause
  else if byte = 0x58 then .equipmentChangeover
  else if byte = 0x41 then .additionalInformationRequested
  else if byte = 0x43 then .regulatoryConcern
  else if byte = 0x45 then .mergerEffective
  else if byte = 0x46 then .etfComponentPricesNotAvailable
  else if byte = 0x4E then .corporateAction
  else if byte = 0x4F then .newSecurityOffering
  else if byte = 0x56 then .intradayIndicativeValueNotAvailable
  else if byte = 0x36 then .suspend
  else if byte = 0x31 then .marketWideCircuitBreakerHaltLevel1
  else if byte = 0x32 then .marketWideCircuitBreakerHaltLevel2
  else .marketWideCircuitBreakerHaltLevel3

def ofByte (byte : UInt8) : HaltCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HaltCondition) : ofByte value.toByte = value := by
  cases value with
  | securityNotDelayedhalted => decide
  | newsReleasedNewsDissemination => decide
  | orderImbalance => decide
  | newsPending => decide
  | luldPause => decide
  | equipmentChangeover => decide
  | additionalInformationRequested => decide
  | regulatoryConcern => decide
  | mergerEffective => decide
  | etfComponentPricesNotAvailable => decide
  | corporateAction => decide
  | newSecurityOffering => decide
  | intradayIndicativeValueNotAvailable => decide
  | suspend => decide
  | marketWideCircuitBreakerHaltLevel1 => decide
  | marketWideCircuitBreakerHaltLevel2 => decide
  | marketWideCircuitBreakerHaltLevel3 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HaltCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HaltCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HaltCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : HaltCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HaltCondition

/-- Ssr Triggering Exchange Id: one byte code -/
def SsrTriggeringExchangeId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x20]

inductive SsrTriggeringExchangeId where
  | nyseAmerican -- Nyse American
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nyseNational -- Nyse National
  | finra -- Finra
  | n24X -- N 24 X
  | miamiPearl -- Miami Pearl
  | nasdaqIse -- Nasdaq Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseTexas -- Nyse Texas
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | nasdaqOmx -- Nasdaq Omx
  | memx -- Memx
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqOmxPsx -- Nasdaq Omx Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | noValue -- No Value
  | unlisted (byte : { byte : UInt8 // byte ∉ SsrTriggeringExchangeId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SsrTriggeringExchangeId

def toByte : SsrTriggeringExchangeId → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqOmxBx => 0x42
  | .nyseNational => 0x43
  | .finra => 0x44
  | .n24X => 0x47
  | .miamiPearl => 0x48
  | .nasdaqIse => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseTexas => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .nasdaqOmx => 0x54
  | .memx => 0x55
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqOmxPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .noValue => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SsrTriggeringExchangeId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqOmxBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finra
  else if byte = 0x47 then .n24X
  else if byte = 0x48 then .miamiPearl
  else if byte = 0x49 then .nasdaqIse
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x54 then .nasdaqOmx
  else if byte = 0x55 then .memx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqOmxPsx
  else if byte = 0x59 then .cboeByx
  else if byte = 0x5A then .cboeBzx
  else .noValue

def ofByte (byte : UInt8) : SsrTriggeringExchangeId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SsrTriggeringExchangeId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqOmxBx => decide
  | nyseNational => decide
  | finra => decide
  | n24X => decide
  | miamiPearl => decide
  | nasdaqIse => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseTexas => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | nasdaqOmx => decide
  | memx => decide
  | iex => decide
  | cbsx => decide
  | nasdaqOmxPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | noValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SsrTriggeringExchangeId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SsrTriggeringExchangeId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SsrTriggeringExchangeId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SsrTriggeringExchangeId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SsrTriggeringExchangeId

/-- Ssr State: one byte code -/
def SsrState.codes : List UInt8 :=
  [0x7E, 0x45]

inductive SsrState where
  | noShortSaleRestrictionInEffect -- No Short Sale Restriction In Effect
  | shortSaleRestrictionInEffect -- Short Sale Restriction In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ SsrState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SsrState

def toByte : SsrState → UInt8
  | .noShortSaleRestrictionInEffect => 0x7E
  | .shortSaleRestrictionInEffect => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SsrState :=
  if byte = 0x7E then .noShortSaleRestrictionInEffect
  else .shortSaleRestrictionInEffect

def ofByte (byte : UInt8) : SsrState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SsrState) : ofByte value.toByte = value := by
  cases value with
  | noShortSaleRestrictionInEffect => decide
  | shortSaleRestrictionInEffect => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SsrState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SsrState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SsrState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SsrState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SsrState

/-- Market State: one byte code -/
def MarketState.codes : List UInt8 :=
  [0x50, 0x45, 0x4F, 0x4C, 0x58]

inductive MarketState where
  | preopening -- Preopening
  | earlySession -- Early Session
  | coreSession -- Core Session
  | lateSessionNonNyseOnly -- Late Session Non Nyse Only
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketState

def toByte : MarketState → UInt8
  | .preopening => 0x50
  | .earlySession => 0x45
  | .coreSession => 0x4F
  | .lateSessionNonNyseOnly => 0x4C
  | .closed => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketState :=
  if byte = 0x50 then .preopening
  else if byte = 0x45 then .earlySession
  else if byte = 0x4F then .coreSession
  else if byte = 0x4C then .lateSessionNonNyseOnly
  else .closed

def ofByte (byte : UInt8) : MarketState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketState) : ofByte value.toByte = value := by
  cases value with
  | preopening => decide
  | earlySession => decide
  | coreSession => decide
  | lateSessionNonNyseOnly => decide
  | closed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketState

/-- Status: one byte code -/
def Status.codes : List UInt8 :=
  [0x30, 0x31, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]

inductive Status where
  | messageWasAccepted -- Message Was Accepted
  | rejectedDueToAnInvalidSourceId -- Rejected Due To An Invalid Source Id
  | rejectedDueToMaximumSequenceRangeSeeThresholdLimits -- Rejected Due To Maximum Sequence Range See Threshold Limits
  | rejectedDueToMaximumRequestInADay -- Rejected Due To Maximum Request In A Day
  | rejectedDueToMaximumNumberOfRefreshRequestsInADay -- Rejected Due To Maximum Number Of Refresh Requests In A Day
  | rejectedRequestMessageSeqNumTtlTimeToLiveIsTooOldUseRefreshToRecoverCurrentStateIfNecessary -- Rejected Request Message Seq Num Ttl Time To Live Is Too Old Use Refresh To Recover Current State If Necessary
  | rejectedDueToAnInvalidChannelId -- Rejected Due To An Invalid Channel Id
  | rejectedDueToAnInvalidProductId -- Rejected Due To An Invalid Product Id
  | rejectedDueTo1InvalidMsgTypeOr2MismatchBetweenMsgTypeAndMsgSize -- Rejected Due To 1 Invalid Msg Type Or 2 Mismatch Between Msg Type And Msg Size
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .messageWasAccepted => 0x30
  | .rejectedDueToAnInvalidSourceId => 0x31
  | .rejectedDueToMaximumSequenceRangeSeeThresholdLimits => 0x33
  | .rejectedDueToMaximumRequestInADay => 0x34
  | .rejectedDueToMaximumNumberOfRefreshRequestsInADay => 0x35
  | .rejectedRequestMessageSeqNumTtlTimeToLiveIsTooOldUseRefreshToRecoverCurrentStateIfNecessary => 0x36
  | .rejectedDueToAnInvalidChannelId => 0x37
  | .rejectedDueToAnInvalidProductId => 0x38
  | .rejectedDueTo1InvalidMsgTypeOr2MismatchBetweenMsgTypeAndMsgSize => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x30 then .messageWasAccepted
  else if byte = 0x31 then .rejectedDueToAnInvalidSourceId
  else if byte = 0x33 then .rejectedDueToMaximumSequenceRangeSeeThresholdLimits
  else if byte = 0x34 then .rejectedDueToMaximumRequestInADay
  else if byte = 0x35 then .rejectedDueToMaximumNumberOfRefreshRequestsInADay
  else if byte = 0x36 then .rejectedRequestMessageSeqNumTtlTimeToLiveIsTooOldUseRefreshToRecoverCurrentStateIfNecessary
  else if byte = 0x37 then .rejectedDueToAnInvalidChannelId
  else if byte = 0x38 then .rejectedDueToAnInvalidProductId
  else .rejectedDueTo1InvalidMsgTypeOr2MismatchBetweenMsgTypeAndMsgSize

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | messageWasAccepted => decide
  | rejectedDueToAnInvalidSourceId => decide
  | rejectedDueToMaximumSequenceRangeSeeThresholdLimits => decide
  | rejectedDueToMaximumRequestInADay => decide
  | rejectedDueToMaximumNumberOfRefreshRequestsInADay => decide
  | rejectedRequestMessageSeqNumTtlTimeToLiveIsTooOldUseRefreshToRecoverCurrentStateIfNecessary => decide
  | rejectedDueToAnInvalidChannelId => decide
  | rejectedDueToAnInvalidProductId => decide
  | rejectedDueTo1InvalidMsgTypeOr2MismatchBetweenMsgTypeAndMsgSize => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Status) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Status × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Status) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Status) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Status

/-- Ask Quote Condition: one byte code -/
def AskQuoteCondition.codes : List UInt8 :=
  [0x43, 0x4F, 0x52, 0x57]

inductive AskQuoteCondition where
  | closing -- Closing
  | openingQuote -- Opening Quote
  | regularQuote -- Regular Quote
  | slowOnTheBidAndAskDueToSetSlowList -- Slow On The Bid And Ask Due To Set Slow List
  | unlisted (byte : { byte : UInt8 // byte ∉ AskQuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AskQuoteCondition

def toByte : AskQuoteCondition → UInt8
  | .closing => 0x43
  | .openingQuote => 0x4F
  | .regularQuote => 0x52
  | .slowOnTheBidAndAskDueToSetSlowList => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AskQuoteCondition :=
  if byte = 0x43 then .closing
  else if byte = 0x4F then .openingQuote
  else if byte = 0x52 then .regularQuote
  else .slowOnTheBidAndAskDueToSetSlowList

def ofByte (byte : UInt8) : AskQuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AskQuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | closing => decide
  | openingQuote => decide
  | regularQuote => decide
  | slowOnTheBidAndAskDueToSetSlowList => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AskQuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AskQuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AskQuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AskQuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AskQuoteCondition

/-- Bid Quote Condition: one byte code -/
def BidQuoteCondition.codes : List UInt8 :=
  [0x43, 0x4F, 0x52, 0x57]

inductive BidQuoteCondition where
  | closing -- Closing
  | openingQuote -- Opening Quote
  | regularQuote -- Regular Quote
  | slowOnTheBidAndAskDueToSetSlowList -- Slow On The Bid And Ask Due To Set Slow List
  | unlisted (byte : { byte : UInt8 // byte ∉ BidQuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BidQuoteCondition

def toByte : BidQuoteCondition → UInt8
  | .closing => 0x43
  | .openingQuote => 0x4F
  | .regularQuote => 0x52
  | .slowOnTheBidAndAskDueToSetSlowList => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BidQuoteCondition :=
  if byte = 0x43 then .closing
  else if byte = 0x4F then .openingQuote
  else if byte = 0x52 then .regularQuote
  else .slowOnTheBidAndAskDueToSetSlowList

def ofByte (byte : UInt8) : BidQuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BidQuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | closing => decide
  | openingQuote => decide
  | regularQuote => decide
  | slowOnTheBidAndAskDueToSetSlowList => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BidQuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BidQuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BidQuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BidQuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BidQuoteCondition

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buy -- Buy
  | sellOffer -- Sell Offer
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sellOffer => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else .sellOffer

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sellOffer => decide
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

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x43, 0x4F, 0x52, 0x57]

inductive QuoteCondition where
  | closing -- Closing
  | openingQuote -- Opening Quote
  | regularQuote -- Regular Quote
  | slowOnTheBidAndAskDueToSetSlowList -- Slow On The Bid And Ask Due To Set Slow List
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .closing => 0x43
  | .openingQuote => 0x4F
  | .regularQuote => 0x52
  | .slowOnTheBidAndAskDueToSetSlowList => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x43 then .closing
  else if byte = 0x4F then .openingQuote
  else if byte = 0x52 then .regularQuote
  else .slowOnTheBidAndAskDueToSetSlowList

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | closing => decide
  | openingQuote => decide
  | regularQuote => decide
  | slowOnTheBidAndAskDueToSetSlowList => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : QuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteCondition

/-- Trade Cond 1: one byte code -/
def TradeCond1.codes : List UInt8 :=
  [0x40, 0x20, 0x43, 0x52]

inductive TradeCond1 where
  | regularSale -- Regular Sale
  | regularSaleTrfOnly -- Regular Sale Trf Only
  | cashTrfOrTexasOnly -- Cash Trf Or Texas Only
  | sellerTrfOnly -- Seller Trf Only
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCond1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCond1

def toByte : TradeCond1 → UInt8
  | .regularSale => 0x40
  | .regularSaleTrfOnly => 0x20
  | .cashTrfOrTexasOnly => 0x43
  | .sellerTrfOnly => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCond1 :=
  if byte = 0x40 then .regularSale
  else if byte = 0x20 then .regularSaleTrfOnly
  else if byte = 0x43 then .cashTrfOrTexasOnly
  else .sellerTrfOnly

def ofByte (byte : UInt8) : TradeCond1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCond1) : ofByte value.toByte = value := by
  cases value with
  | regularSale => decide
  | regularSaleTrfOnly => decide
  | cashTrfOrTexasOnly => decide
  | sellerTrfOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCond1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCond1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCond1) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCond1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCond1

/-- Trade Cond 2: one byte code -/
def TradeCond2.codes : List UInt8 :=
  [0x20, 0x46, 0x4F, 0x34, 0x35, 0x36, 0x37, 0x39]

inductive TradeCond2 where
  | na -- Na
  | intermarketSweepOrder -- Intermarket Sweep Order
  | marketCenterOpeningTrade -- Market Center Opening Trade
  | derivativelyPricedTrfOnly -- Derivatively Priced Trf Only
  | reopeningTrade -- Reopening Trade
  | marketCenterClosingTrade -- Market Center Closing Trade
  | qualifiedContingentTradeTrfOrTexasOnly -- Qualified Contingent Trade Trf Or Texas Only
  | correctedConsolidatedClose -- Corrected Consolidated Close
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCond2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCond2

def toByte : TradeCond2 → UInt8
  | .na => 0x20
  | .intermarketSweepOrder => 0x46
  | .marketCenterOpeningTrade => 0x4F
  | .derivativelyPricedTrfOnly => 0x34
  | .reopeningTrade => 0x35
  | .marketCenterClosingTrade => 0x36
  | .qualifiedContingentTradeTrfOrTexasOnly => 0x37
  | .correctedConsolidatedClose => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCond2 :=
  if byte = 0x20 then .na
  else if byte = 0x46 then .intermarketSweepOrder
  else if byte = 0x4F then .marketCenterOpeningTrade
  else if byte = 0x34 then .derivativelyPricedTrfOnly
  else if byte = 0x35 then .reopeningTrade
  else if byte = 0x36 then .marketCenterClosingTrade
  else if byte = 0x37 then .qualifiedContingentTradeTrfOrTexasOnly
  else .correctedConsolidatedClose

def ofByte (byte : UInt8) : TradeCond2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCond2) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | intermarketSweepOrder => decide
  | marketCenterOpeningTrade => decide
  | derivativelyPricedTrfOnly => decide
  | reopeningTrade => decide
  | marketCenterClosingTrade => decide
  | qualifiedContingentTradeTrfOrTexasOnly => decide
  | correctedConsolidatedClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCond2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCond2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCond2) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCond2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCond2

/-- Trade Cond 3: one byte code -/
def TradeCond3.codes : List UInt8 :=
  [0x20, 0x54, 0x55, 0x5A]

inductive TradeCond3 where
  | na -- Na
  | extendedHoursTrade -- Extended Hours Trade
  | extendedHoursSoldOutOfSequence -- Extended Hours Sold Out Of Sequence
  | sold -- Sold
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCond3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCond3

def toByte : TradeCond3 → UInt8
  | .na => 0x20
  | .extendedHoursTrade => 0x54
  | .extendedHoursSoldOutOfSequence => 0x55
  | .sold => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCond3 :=
  if byte = 0x20 then .na
  else if byte = 0x54 then .extendedHoursTrade
  else if byte = 0x55 then .extendedHoursSoldOutOfSequence
  else .sold

def ofByte (byte : UInt8) : TradeCond3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCond3) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | extendedHoursTrade => decide
  | extendedHoursSoldOutOfSequence => decide
  | sold => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCond3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCond3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCond3) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCond3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCond3

/-- Trade Cond 4: one byte code -/
def TradeCond4.codes : List UInt8 :=
  [0x20, 0x49, 0x4D, 0x51, 0x56, 0x50, 0x57]

inductive TradeCond4 where
  | na -- Na
  | oddLotTrade -- Odd Lot Trade
  | officialClosingPrice -- Official Closing Price
  | officialOpenPrice -- Official Open Price
  | contingentTradeTrfOrTexasOnly -- Contingent Trade Trf Or Texas Only
  | priorReferencePriceTrfOnly -- Prior Reference Price Trf Only
  | weightedAveragePriceTrfOnly -- Weighted Average Price Trf Only
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCond4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCond4

def toByte : TradeCond4 → UInt8
  | .na => 0x20
  | .oddLotTrade => 0x49
  | .officialClosingPrice => 0x4D
  | .officialOpenPrice => 0x51
  | .contingentTradeTrfOrTexasOnly => 0x56
  | .priorReferencePriceTrfOnly => 0x50
  | .weightedAveragePriceTrfOnly => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCond4 :=
  if byte = 0x20 then .na
  else if byte = 0x49 then .oddLotTrade
  else if byte = 0x4D then .officialClosingPrice
  else if byte = 0x51 then .officialOpenPrice
  else if byte = 0x56 then .contingentTradeTrfOrTexasOnly
  else if byte = 0x50 then .priorReferencePriceTrfOnly
  else .weightedAveragePriceTrfOnly

def ofByte (byte : UInt8) : TradeCond4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCond4) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | oddLotTrade => decide
  | officialClosingPrice => decide
  | officialOpenPrice => decide
  | contingentTradeTrfOrTexasOnly => decide
  | priorReferencePriceTrfOnly => decide
  | weightedAveragePriceTrfOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCond4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCond4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCond4) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCond4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCond4

/-- Trade Condition 1: one byte code -/
def TradeCondition1.codes : List UInt8 :=
  [0x40, 0x20, 0x43, 0x52]

inductive TradeCondition1 where
  | regularSale -- Regular Sale
  | regularSaleForTrf -- Regular Sale For Trf
  | cashTrfOrTexasOnly -- Cash Trf Or Texas Only
  | sellerTrfOnly -- Seller Trf Only
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCondition1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCondition1

def toByte : TradeCondition1 → UInt8
  | .regularSale => 0x40
  | .regularSaleForTrf => 0x20
  | .cashTrfOrTexasOnly => 0x43
  | .sellerTrfOnly => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCondition1 :=
  if byte = 0x40 then .regularSale
  else if byte = 0x20 then .regularSaleForTrf
  else if byte = 0x43 then .cashTrfOrTexasOnly
  else .sellerTrfOnly

def ofByte (byte : UInt8) : TradeCondition1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCondition1) : ofByte value.toByte = value := by
  cases value with
  | regularSale => decide
  | regularSaleForTrf => decide
  | cashTrfOrTexasOnly => decide
  | sellerTrfOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCondition1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCondition1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCondition1) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCondition1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCondition1

/-- Trade Condition 2: one byte code -/
def TradeCondition2.codes : List UInt8 :=
  [0x20, 0x46, 0x4F, 0x34, 0x35, 0x36, 0x37, 0x39]

inductive TradeCondition2 where
  | na -- Na
  | intermarketSweepOrder -- Intermarket Sweep Order
  | marketCenterOpeningTrade -- Market Center Opening Trade
  | derivativelyPricedTrfOnly -- Derivatively Priced Trf Only
  | marketCenterReopeningTrade -- Market Center Reopening Trade
  | marketCenterClosingTrade -- Market Center Closing Trade
  | qualifiedContingentTradeTrfOrTexasOnly -- Qualified Contingent Trade Trf Or Texas Only
  | correctedLastSalePrice -- Corrected Last Sale Price
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCondition2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCondition2

def toByte : TradeCondition2 → UInt8
  | .na => 0x20
  | .intermarketSweepOrder => 0x46
  | .marketCenterOpeningTrade => 0x4F
  | .derivativelyPricedTrfOnly => 0x34
  | .marketCenterReopeningTrade => 0x35
  | .marketCenterClosingTrade => 0x36
  | .qualifiedContingentTradeTrfOrTexasOnly => 0x37
  | .correctedLastSalePrice => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCondition2 :=
  if byte = 0x20 then .na
  else if byte = 0x46 then .intermarketSweepOrder
  else if byte = 0x4F then .marketCenterOpeningTrade
  else if byte = 0x34 then .derivativelyPricedTrfOnly
  else if byte = 0x35 then .marketCenterReopeningTrade
  else if byte = 0x36 then .marketCenterClosingTrade
  else if byte = 0x37 then .qualifiedContingentTradeTrfOrTexasOnly
  else .correctedLastSalePrice

def ofByte (byte : UInt8) : TradeCondition2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCondition2) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | intermarketSweepOrder => decide
  | marketCenterOpeningTrade => decide
  | derivativelyPricedTrfOnly => decide
  | marketCenterReopeningTrade => decide
  | marketCenterClosingTrade => decide
  | qualifiedContingentTradeTrfOrTexasOnly => decide
  | correctedLastSalePrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCondition2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCondition2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCondition2) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCondition2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCondition2

/-- Trade Condition 3: one byte code -/
def TradeCondition3.codes : List UInt8 :=
  [0x20, 0x54, 0x55, 0x5A]

inductive TradeCondition3 where
  | na -- Na
  | extendedHoursTrade -- Extended Hours Trade
  | extendedHoursSoldOutOfSequence -- Extended Hours Sold Out Of Sequence
  | sold -- Sold
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCondition3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCondition3

def toByte : TradeCondition3 → UInt8
  | .na => 0x20
  | .extendedHoursTrade => 0x54
  | .extendedHoursSoldOutOfSequence => 0x55
  | .sold => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCondition3 :=
  if byte = 0x20 then .na
  else if byte = 0x54 then .extendedHoursTrade
  else if byte = 0x55 then .extendedHoursSoldOutOfSequence
  else .sold

def ofByte (byte : UInt8) : TradeCondition3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCondition3) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | extendedHoursTrade => decide
  | extendedHoursSoldOutOfSequence => decide
  | sold => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCondition3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCondition3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCondition3) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCondition3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCondition3

/-- Trade Condition 4: one byte code -/
def TradeCondition4.codes : List UInt8 :=
  [0x40, 0x20, 0x49, 0x4D, 0x51, 0x56, 0x50, 0x57]

inductive TradeCondition4 where
  | regularSale -- Regular Sale
  | na -- Na
  | oddLotTrade -- Odd Lot Trade
  | officialClosingPrice -- Official Closing Price
  | officialOpenPrice -- Official Open Price
  | contingentTradeTrfOrTexasOnly -- Contingent Trade Trf Or Texas Only
  | priorReferencePriceTrfOnly -- Prior Reference Price Trf Only
  | weightedAveragePriceTrfOnly -- Weighted Average Price Trf Only
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCondition4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCondition4

def toByte : TradeCondition4 → UInt8
  | .regularSale => 0x40
  | .na => 0x20
  | .oddLotTrade => 0x49
  | .officialClosingPrice => 0x4D
  | .officialOpenPrice => 0x51
  | .contingentTradeTrfOrTexasOnly => 0x56
  | .priorReferencePriceTrfOnly => 0x50
  | .weightedAveragePriceTrfOnly => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCondition4 :=
  if byte = 0x40 then .regularSale
  else if byte = 0x20 then .na
  else if byte = 0x49 then .oddLotTrade
  else if byte = 0x4D then .officialClosingPrice
  else if byte = 0x51 then .officialOpenPrice
  else if byte = 0x56 then .contingentTradeTrfOrTexasOnly
  else if byte = 0x50 then .priorReferencePriceTrfOnly
  else .weightedAveragePriceTrfOnly

def ofByte (byte : UInt8) : TradeCondition4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCondition4) : ofByte value.toByte = value := by
  cases value with
  | regularSale => decide
  | na => decide
  | oddLotTrade => decide
  | officialClosingPrice => decide
  | officialOpenPrice => decide
  | contingentTradeTrfOrTexasOnly => decide
  | priorReferencePriceTrfOnly => decide
  | weightedAveragePriceTrfOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCondition4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCondition4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCondition4) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCondition4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCondition4

/-- Send Time: 8 bytes -/
structure SendTime where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace SendTime

def encode (message : SendTime) : List UInt8 :=
  encodeUIntLE 4 message.seconds
    ++ (encodeUIntLE 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (SendTime × List UInt8) := do
  let (seconds, bytes) ← decodeUIntLE 4 bytes
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : SendTime) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SendTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SendTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SendTime

/-- Sequence Number Reset Message: 10 bytes -/
structure SequenceNumberResetMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  productId : BitVec 8
  channelId : BitVec 8
  deriving DecidableEq, Repr

namespace SequenceNumberResetMessage

def encode (message : SequenceNumberResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId)))

def decode (bytes : List UInt8) : Option (SequenceNumberResetMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  pure ({ sourceTime, sourceTimeNs, productId, channelId }, bytes)

@[simp] theorem encode_length (message : SequenceNumberResetMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SequenceNumberResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceNumberResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceNumberResetMessage

/-- Source Time Reference Message: 12 bytes -/
structure SourceTimeReferenceMessage where
  id : BitVec 32
  symbolSeqNum : BitVec 32
  sourceTime : BitVec 32
  deriving DecidableEq, Repr

namespace SourceTimeReferenceMessage

def encode (message : SourceTimeReferenceMessage) : List UInt8 :=
  encodeUIntLE 4 message.id
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.sourceTime))

def decode (bytes : List UInt8) : Option (SourceTimeReferenceMessage × List UInt8) := do
  let (id, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  pure ({ id, symbolSeqNum, sourceTime }, bytes)

@[simp] theorem encode_length (message : SourceTimeReferenceMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SourceTimeReferenceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SourceTimeReferenceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SourceTimeReferenceMessage

/-- Symbol Index Mapping Message: 40 bytes -/
structure SymbolIndexMappingMessage where
  symbolIndex : BitVec 32
  symbol : Alpha 11
  reserved1 : Alpha 1
  marketId : BitVec 16
  systemId : BitVec 8
  exchangeCode : ExchangeCode
  priceScaleCode : BitVec 8
  securityType : SecurityType
  lotSize : BitVec 16
  prevClosePrice : BitVec 32
  prevCloseVolume : BitVec 32
  priceResolution : BitVec 8
  roundLot : RoundLot
  mpv : BitVec 16
  unitOfTrade : BitVec 16
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace SymbolIndexMappingMessage

def encode (message : SymbolIndexMappingMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUIntLE 1 message.systemId
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (encodeUIntLE 1 message.priceScaleCode
    ++ (SecurityType.encode message.securityType
    ++ (encodeUIntLE 2 message.lotSize
    ++ (encodeUIntLE 4 message.prevClosePrice
    ++ (encodeUIntLE 4 message.prevCloseVolume
    ++ (encodeUIntLE 1 message.priceResolution
    ++ (RoundLot.encode message.roundLot
    ++ (encodeUIntLE 2 message.mpv
    ++ (encodeUIntLE 2 message.unitOfTrade
    ++ (Alpha.encode message.reserved2)))))))))))))))

def decode (bytes : List UInt8) : Option (SymbolIndexMappingMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 11 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (systemId, bytes) ← decodeUIntLE 1 bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (priceScaleCode, bytes) ← decodeUIntLE 1 bytes
  let (securityType, bytes) ← SecurityType.decode bytes
  let (lotSize, bytes) ← decodeUIntLE 2 bytes
  let (prevClosePrice, bytes) ← decodeUIntLE 4 bytes
  let (prevCloseVolume, bytes) ← decodeUIntLE 4 bytes
  let (priceResolution, bytes) ← decodeUIntLE 1 bytes
  let (roundLot, bytes) ← RoundLot.decode bytes
  let (mpv, bytes) ← decodeUIntLE 2 bytes
  let (unitOfTrade, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ symbolIndex, symbol, reserved1, marketId, systemId, exchangeCode, priceScaleCode, securityType, lotSize, prevClosePrice, prevCloseVolume, priceResolution, roundLot, mpv, unitOfTrade, reserved2 }, bytes)

@[simp] theorem encode_length (message : SymbolIndexMappingMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ExchangeCode.encode_length, SecurityType.encode_length, RoundLot.encode_length]

theorem encode_length_pos (message : SymbolIndexMappingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolIndexMappingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, RoundLot.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolIndexMappingMessage

/-- Symbol Clear Message: 18 bytes -/
structure SymbolClearMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  nextSourceSeqNum : BitVec 32
  marketId : BitVec 16
  deriving DecidableEq, Repr

namespace SymbolClearMessage

def encode (message : SymbolClearMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.nextSourceSeqNum
    ++ (encodeUIntLE 2 message.marketId))))

def decode (bytes : List UInt8) : Option (SymbolClearMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (nextSourceSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, nextSourceSeqNum, marketId }, bytes)

@[simp] theorem encode_length (message : SymbolClearMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SymbolClearMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolClearMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SymbolClearMessage

/-- Security Status Message: 42 bytes -/
structure SecurityStatusMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  securityStatus : SecurityStatus
  haltCondition : HaltCondition
  marketId : BitVec 16
  reserved2 : Alpha 2
  price1 : BitVec 32
  price2 : BitVec 32
  ssrTriggeringExchangeId : SsrTriggeringExchangeId
  ssrTriggeringVolume : BitVec 32
  time : BitVec 32
  ssrState : SsrState
  marketState : MarketState
  sessionState : Alpha 1
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (SecurityStatus.encode message.securityStatus
    ++ (HaltCondition.encode message.haltCondition
    ++ (encodeUIntLE 2 message.marketId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUIntLE 4 message.price1
    ++ (encodeUIntLE 4 message.price2
    ++ (SsrTriggeringExchangeId.encode message.ssrTriggeringExchangeId
    ++ (encodeUIntLE 4 message.ssrTriggeringVolume
    ++ (encodeUIntLE 4 message.time
    ++ (SsrState.encode message.ssrState
    ++ (MarketState.encode message.marketState
    ++ (Alpha.encode message.sessionState)))))))))))))))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (haltCondition, bytes) ← HaltCondition.decode bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (price1, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 4 bytes
  let (ssrTriggeringExchangeId, bytes) ← SsrTriggeringExchangeId.decode bytes
  let (ssrTriggeringVolume, bytes) ← decodeUIntLE 4 bytes
  let (time, bytes) ← decodeUIntLE 4 bytes
  let (ssrState, bytes) ← SsrState.decode bytes
  let (marketState, bytes) ← MarketState.decode bytes
  let (sessionState, bytes) ← Alpha.decode 1 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, securityStatus, haltCondition, marketId, reserved2, price1, price2, ssrTriggeringExchangeId, ssrTriggeringVolume, time, ssrState, marketState, sessionState }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityStatus.encode_length, HaltCondition.encode_length, Alpha.encode_length, SsrTriggeringExchangeId.encode_length, SsrState.encode_length, MarketState.encode_length]

theorem encode_length_pos (message : SecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HaltCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SsrTriggeringExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SsrState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketState.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityStatusMessage

/-- Retransmission Request Message: 20 bytes -/
structure RetransmissionRequestMessage where
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  sourceId : Alpha 10
  productId : BitVec 8
  channelId : BitVec 8
  deriving DecidableEq, Repr

namespace RetransmissionRequestMessage

def encode (message : RetransmissionRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.beginSeqNum
    ++ (encodeUIntLE 4 message.endSeqNum
    ++ (Alpha.encode message.sourceId
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId))))

def decode (bytes : List UInt8) : Option (RetransmissionRequestMessage × List UInt8) := do
  let (beginSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (sourceId, bytes) ← Alpha.decode 10 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  pure ({ beginSeqNum, endSeqNum, sourceId, productId, channelId }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RetransmissionRequestMessage

/-- Symbol Index Mapping Request Message: 17 bytes -/
structure SymbolIndexMappingRequestMessage where
  symbolIndex : BitVec 32
  sourceId : Alpha 10
  productId : BitVec 8
  channelId : BitVec 8
  retransmitMethod : BitVec 8
  deriving DecidableEq, Repr

namespace SymbolIndexMappingRequestMessage

def encode (message : SymbolIndexMappingRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (Alpha.encode message.sourceId
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId
    ++ (encodeUIntLE 1 message.retransmitMethod))))

def decode (bytes : List UInt8) : Option (SymbolIndexMappingRequestMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (sourceId, bytes) ← Alpha.decode 10 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  let (retransmitMethod, bytes) ← decodeUIntLE 1 bytes
  pure ({ symbolIndex, sourceId, productId, channelId, retransmitMethod }, bytes)

@[simp] theorem encode_length (message : SymbolIndexMappingRequestMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SymbolIndexMappingRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolIndexMappingRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SymbolIndexMappingRequestMessage

/-- Refresh Request Message: 16 bytes -/
structure RefreshRequestMessage where
  symbolIndex : BitVec 32
  sourceId : Alpha 10
  productId : BitVec 8
  channelId : BitVec 8
  deriving DecidableEq, Repr

namespace RefreshRequestMessage

def encode (message : RefreshRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (Alpha.encode message.sourceId
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId)))

def decode (bytes : List UInt8) : Option (RefreshRequestMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (sourceId, bytes) ← Alpha.decode 10 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  pure ({ symbolIndex, sourceId, productId, channelId }, bytes)

@[simp] theorem encode_length (message : RefreshRequestMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RefreshRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RefreshRequestMessage

/-- Message Unavailable Message: 10 bytes -/
structure MessageUnavailableMessage where
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  productId : BitVec 8
  channelId : BitVec 8
  deriving DecidableEq, Repr

namespace MessageUnavailableMessage

def encode (message : MessageUnavailableMessage) : List UInt8 :=
  encodeUIntLE 4 message.beginSeqNum
    ++ (encodeUIntLE 4 message.endSeqNum
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId)))

def decode (bytes : List UInt8) : Option (MessageUnavailableMessage × List UInt8) := do
  let (beginSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  pure ({ beginSeqNum, endSeqNum, productId, channelId }, bytes)

@[simp] theorem encode_length (message : MessageUnavailableMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MessageUnavailableMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageUnavailableMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MessageUnavailableMessage

/-- Full Refresh Header: 8 bytes -/
structure FullRefreshHeader where
  lastSeqNum : BitVec 32
  lastSymbolSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace FullRefreshHeader

def encode (message : FullRefreshHeader) : List UInt8 :=
  encodeUIntLE 4 message.lastSeqNum
    ++ (encodeUIntLE 4 message.lastSymbolSeqNum)

def decode (bytes : List UInt8) : Option (FullRefreshHeader × List UInt8) := do
  let (lastSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (lastSymbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ lastSeqNum, lastSymbolSeqNum }, bytes)

@[simp] theorem encode_length (message : FullRefreshHeader) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : FullRefreshHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FullRefreshHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end FullRefreshHeader

/-- Any Refresh Header Layout, selected by Current Refresh Pkt -/
inductive RefreshHeaderLayout where
  | fullRefreshHeader (message : FullRefreshHeader) -- 1
  deriving DecidableEq, Repr

namespace RefreshHeaderLayout

/-- The Current Refresh Pkt each message is sent under -/
def tag : RefreshHeaderLayout → BitVec 16
  | .fullRefreshHeader _ => 1

def encode : RefreshHeaderLayout → List UInt8
  | .fullRefreshHeader message => FullRefreshHeader.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : RefreshHeaderLayout) : (encode message).length ≤ 8 := by
  cases message with
  | fullRefreshHeader inner =>
    simp only [encode, FullRefreshHeader.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (RefreshHeaderLayout × List UInt8) :=
  if tag = 1 then (FullRefreshHeader.decode bytes).map fun (message, rest) => (.fullRefreshHeader message, rest)
  else none

@[simp] theorem decode_encode (message : RefreshHeaderLayout) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end RefreshHeaderLayout

/-- Refresh Header Message -/
structure RefreshHeaderMessage where
  totalRefreshPkts : BitVec 16
  refreshHeaderLayout : RefreshHeaderLayout
  deriving DecidableEq, Repr

namespace RefreshHeaderMessage

def encode (message : RefreshHeaderMessage) : List UInt8 :=
  encodeUIntLE 2 (RefreshHeaderLayout.tag message.refreshHeaderLayout)
    ++ (encodeUIntLE 2 message.totalRefreshPkts
    ++ (RefreshHeaderLayout.encode message.refreshHeaderLayout))

def decode (bytes : List UInt8) : Option (RefreshHeaderMessage × List UInt8) := do
  let (currentRefreshPkt, bytes) ← decodeUIntLE 2 bytes
  let (totalRefreshPkts, bytes) ← decodeUIntLE 2 bytes
  let (refreshHeaderLayout, bytes) ← RefreshHeaderLayout.decode currentRefreshPkt bytes
  pure ({ totalRefreshPkts, refreshHeaderLayout }, bytes)

theorem encode_length_pos (message : RefreshHeaderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RefreshHeaderMessage) : (encode message).length ≤ 12 := by
  unfold encode
  cases message.refreshHeaderLayout with
  | fullRefreshHeader inner =>
    simp only [RefreshHeaderLayout.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, FullRefreshHeader.encode_length]
    omega

@[simp] theorem decode_encode (message : RefreshHeaderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [RefreshHeaderLayout.decode_encode, some_bind]
  rfl

end RefreshHeaderMessage

/-- Request Response Message: 25 bytes -/
structure RequestResponseMessage where
  requestSeqNum : BitVec 32
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  sourceId : Alpha 10
  productId : BitVec 8
  channelId : BitVec 8
  status : Status
  deriving DecidableEq, Repr

namespace RequestResponseMessage

def encode (message : RequestResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestSeqNum
    ++ (encodeUIntLE 4 message.beginSeqNum
    ++ (encodeUIntLE 4 message.endSeqNum
    ++ (Alpha.encode message.sourceId
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId
    ++ (Status.encode message.status))))))

def decode (bytes : List UInt8) : Option (RequestResponseMessage × List UInt8) := do
  let (requestSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (beginSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (sourceId, bytes) ← Alpha.decode 10 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  let (status, bytes) ← Status.decode bytes
  pure ({ requestSeqNum, beginSeqNum, endSeqNum, sourceId, productId, channelId, status }, bytes)

@[simp] theorem encode_length (message : RequestResponseMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Status.encode_length]

theorem encode_length_pos (message : RequestResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Status.decode_encode, some_bind]
  rfl

end RequestResponseMessage

/-- Heartbeat Response Message: 10 bytes -/
structure HeartbeatResponseMessage where
  sourceId : Alpha 10
  deriving DecidableEq, Repr

namespace HeartbeatResponseMessage

def encode (message : HeartbeatResponseMessage) : List UInt8 :=
  Alpha.encode message.sourceId

def decode (bytes : List UInt8) : Option (HeartbeatResponseMessage × List UInt8) := do
  let (sourceId, bytes) ← Alpha.decode 10 bytes
  pure ({ sourceId }, bytes)

@[simp] theorem encode_length (message : HeartbeatResponseMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : HeartbeatResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end HeartbeatResponseMessage

/-- Best Quotes Message: 31 bytes -/
structure BestQuotesMessage where
  symbolIndex : BitVec 32
  symbolSeqNumber : BitVec 32
  askPrice : BitVec 32
  askVolume : BitVec 32
  bidPrice : BitVec 32
  bidVolume : BitVec 32
  askQuoteCondition : AskQuoteCondition
  bidQuoteCondition : BidQuoteCondition
  retailPricingIndicator : BitVec 8
  marketIdOfBestAsk : BitVec 16
  marketIdOfBestBid : BitVec 16
  deriving DecidableEq, Repr

namespace BestQuotesMessage

def encode (message : BestQuotesMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNumber
    ++ (encodeUIntLE 4 message.askPrice
    ++ (encodeUIntLE 4 message.askVolume
    ++ (encodeUIntLE 4 message.bidPrice
    ++ (encodeUIntLE 4 message.bidVolume
    ++ (AskQuoteCondition.encode message.askQuoteCondition
    ++ (BidQuoteCondition.encode message.bidQuoteCondition
    ++ (encodeUIntLE 1 message.retailPricingIndicator
    ++ (encodeUIntLE 2 message.marketIdOfBestAsk
    ++ (encodeUIntLE 2 message.marketIdOfBestBid))))))))))

def decode (bytes : List UInt8) : Option (BestQuotesMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNumber, bytes) ← decodeUIntLE 4 bytes
  let (askPrice, bytes) ← decodeUIntLE 4 bytes
  let (askVolume, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 4 bytes
  let (bidVolume, bytes) ← decodeUIntLE 4 bytes
  let (askQuoteCondition, bytes) ← AskQuoteCondition.decode bytes
  let (bidQuoteCondition, bytes) ← BidQuoteCondition.decode bytes
  let (retailPricingIndicator, bytes) ← decodeUIntLE 1 bytes
  let (marketIdOfBestAsk, bytes) ← decodeUIntLE 2 bytes
  let (marketIdOfBestBid, bytes) ← decodeUIntLE 2 bytes
  pure ({ symbolIndex, symbolSeqNumber, askPrice, askVolume, bidPrice, bidVolume, askQuoteCondition, bidQuoteCondition, retailPricingIndicator, marketIdOfBestAsk, marketIdOfBestBid }, bytes)

@[simp] theorem encode_length (message : BestQuotesMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, AskQuoteCondition.encode_length, BidQuoteCondition.encode_length]

theorem encode_length_pos (message : BestQuotesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestQuotesMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, AskQuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidQuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BestQuotesMessage

/-- Consolidated Single Sided Quote Message: 21 bytes -/
structure ConsolidatedSingleSidedQuoteMessage where
  symbolIndex : BitVec 32
  symbolSeqNumber : BitVec 32
  side : Side
  price : BitVec 32
  volume : BitVec 32
  quoteCondition : QuoteCondition
  retailPricingIndicator : BitVec 8
  marketId : BitVec 16
  deriving DecidableEq, Repr

namespace ConsolidatedSingleSidedQuoteMessage

def encode (message : ConsolidatedSingleSidedQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNumber
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUIntLE 1 message.retailPricingIndicator
    ++ (encodeUIntLE 2 message.marketId)))))))

def decode (bytes : List UInt8) : Option (ConsolidatedSingleSidedQuoteMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNumber, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (retailPricingIndicator, bytes) ← decodeUIntLE 1 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  pure ({ symbolIndex, symbolSeqNumber, side, price, volume, quoteCondition, retailPricingIndicator, marketId }, bytes)

@[simp] theorem encode_length (message : ConsolidatedSingleSidedQuoteMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : ConsolidatedSingleSidedQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedSingleSidedQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConsolidatedSingleSidedQuoteMessage

/-- Trf Fractional Trade Message: 46 bytes -/
structure TrfFractionalTradeMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  fractionalVolume : BitVec 64
  tradeCond1 : TradeCond1
  tradeCond2 : TradeCond2
  tradeCond3 : TradeCond3
  tradeCond4 : TradeCond4
  execDayTime : BitVec 32
  execDayTimeNs : BitVec 32
  marketId : BitVec 16
  deriving DecidableEq, Repr

namespace TrfFractionalTradeMessage

def encode (message : TrfFractionalTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 8 message.fractionalVolume
    ++ (TradeCond1.encode message.tradeCond1
    ++ (TradeCond2.encode message.tradeCond2
    ++ (TradeCond3.encode message.tradeCond3
    ++ (TradeCond4.encode message.tradeCond4
    ++ (encodeUIntLE 4 message.execDayTime
    ++ (encodeUIntLE 4 message.execDayTimeNs
    ++ (encodeUIntLE 2 message.marketId)))))))))))))

def decode (bytes : List UInt8) : Option (TrfFractionalTradeMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (fractionalVolume, bytes) ← decodeUIntLE 8 bytes
  let (tradeCond1, bytes) ← TradeCond1.decode bytes
  let (tradeCond2, bytes) ← TradeCond2.decode bytes
  let (tradeCond3, bytes) ← TradeCond3.decode bytes
  let (tradeCond4, bytes) ← TradeCond4.decode bytes
  let (execDayTime, bytes) ← decodeUIntLE 4 bytes
  let (execDayTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, tradeId, price, fractionalVolume, tradeCond1, tradeCond2, tradeCond3, tradeCond4, execDayTime, execDayTimeNs, marketId }, bytes)

@[simp] theorem encode_length (message : TrfFractionalTradeMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCond1.encode_length, TradeCond2.encode_length, TradeCond3.encode_length, TradeCond4.encode_length]

theorem encode_length_pos (message : TrfFractionalTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TrfFractionalTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeCond1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCond2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCond3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCond4.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TrfFractionalTradeMessage

/-- Consolidated Trade Message: 34 bytes -/
structure ConsolidatedTradeMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNumber : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  tradeCondition1 : TradeCondition1
  tradeCondition2 : TradeCondition2
  tradeCondition3 : TradeCondition3
  tradeCondition4 : TradeCondition4
  marketId : BitVec 16
  deriving DecidableEq, Repr

namespace ConsolidatedTradeMessage

def encode (message : ConsolidatedTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNumber
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (TradeCondition1.encode message.tradeCondition1
    ++ (TradeCondition2.encode message.tradeCondition2
    ++ (TradeCondition3.encode message.tradeCondition3
    ++ (TradeCondition4.encode message.tradeCondition4
    ++ (encodeUIntLE 2 message.marketId)))))))))))

def decode (bytes : List UInt8) : Option (ConsolidatedTradeMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNumber, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (tradeCondition1, bytes) ← TradeCondition1.decode bytes
  let (tradeCondition2, bytes) ← TradeCondition2.decode bytes
  let (tradeCondition3, bytes) ← TradeCondition3.decode bytes
  let (tradeCondition4, bytes) ← TradeCondition4.decode bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNumber, tradeId, price, volume, tradeCondition1, tradeCondition2, tradeCondition3, tradeCondition4, marketId }, bytes)

@[simp] theorem encode_length (message : ConsolidatedTradeMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCondition1.encode_length, TradeCondition2.encode_length, TradeCondition3.encode_length, TradeCondition4.encode_length]

theorem encode_length_pos (message : ConsolidatedTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeCondition1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCondition2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCondition3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCondition4.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConsolidatedTradeMessage

/-- Consolidated Trade Cancel Message: 22 bytes -/
structure ConsolidatedTradeCancelMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNumber : BitVec 32
  originalTradeId : BitVec 32
  marketId : BitVec 16
  deriving DecidableEq, Repr

namespace ConsolidatedTradeCancelMessage

def encode (message : ConsolidatedTradeCancelMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNumber
    ++ (encodeUIntLE 4 message.originalTradeId
    ++ (encodeUIntLE 2 message.marketId)))))

def decode (bytes : List UInt8) : Option (ConsolidatedTradeCancelMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNumber, bytes) ← decodeUIntLE 4 bytes
  let (originalTradeId, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNumber, originalTradeId, marketId }, bytes)

@[simp] theorem encode_length (message : ConsolidatedTradeCancelMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ConsolidatedTradeCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedTradeCancelMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConsolidatedTradeCancelMessage

/-- Trf Fractional Trade Correction Message: 50 bytes -/
structure TrfFractionalTradeCorrectionMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  originalTradeId : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  fractionalVolume : BitVec 64
  tradeCond1 : TradeCond1
  tradeCond2 : TradeCond2
  tradeCond3 : TradeCond3
  tradeCond4 : TradeCond4
  execDayTime : BitVec 32
  execDayTimeNs : BitVec 32
  marketId : BitVec 16
  deriving DecidableEq, Repr

namespace TrfFractionalTradeCorrectionMessage

def encode (message : TrfFractionalTradeCorrectionMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.originalTradeId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 8 message.fractionalVolume
    ++ (TradeCond1.encode message.tradeCond1
    ++ (TradeCond2.encode message.tradeCond2
    ++ (TradeCond3.encode message.tradeCond3
    ++ (TradeCond4.encode message.tradeCond4
    ++ (encodeUIntLE 4 message.execDayTime
    ++ (encodeUIntLE 4 message.execDayTimeNs
    ++ (encodeUIntLE 2 message.marketId))))))))))))))

def decode (bytes : List UInt8) : Option (TrfFractionalTradeCorrectionMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (originalTradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (fractionalVolume, bytes) ← decodeUIntLE 8 bytes
  let (tradeCond1, bytes) ← TradeCond1.decode bytes
  let (tradeCond2, bytes) ← TradeCond2.decode bytes
  let (tradeCond3, bytes) ← TradeCond3.decode bytes
  let (tradeCond4, bytes) ← TradeCond4.decode bytes
  let (execDayTime, bytes) ← decodeUIntLE 4 bytes
  let (execDayTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, originalTradeId, tradeId, price, fractionalVolume, tradeCond1, tradeCond2, tradeCond3, tradeCond4, execDayTime, execDayTimeNs, marketId }, bytes)

@[simp] theorem encode_length (message : TrfFractionalTradeCorrectionMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCond1.encode_length, TradeCond2.encode_length, TradeCond3.encode_length, TradeCond4.encode_length]

theorem encode_length_pos (message : TrfFractionalTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TrfFractionalTradeCorrectionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeCond1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCond2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCond3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCond4.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TrfFractionalTradeCorrectionMessage

/-- Consolidated Trade Correction Message: 38 bytes -/
structure ConsolidatedTradeCorrectionMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNumber : BitVec 32
  originalTradeId : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  tradeCondition1 : TradeCondition1
  tradeCondition2 : TradeCondition2
  tradeCondition3 : TradeCondition3
  tradeCondition4 : TradeCondition4
  marketId : BitVec 16
  deriving DecidableEq, Repr

namespace ConsolidatedTradeCorrectionMessage

def encode (message : ConsolidatedTradeCorrectionMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNumber
    ++ (encodeUIntLE 4 message.originalTradeId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (TradeCondition1.encode message.tradeCondition1
    ++ (TradeCondition2.encode message.tradeCondition2
    ++ (TradeCondition3.encode message.tradeCondition3
    ++ (TradeCondition4.encode message.tradeCondition4
    ++ (encodeUIntLE 2 message.marketId))))))))))))

def decode (bytes : List UInt8) : Option (ConsolidatedTradeCorrectionMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNumber, bytes) ← decodeUIntLE 4 bytes
  let (originalTradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (tradeCondition1, bytes) ← TradeCondition1.decode bytes
  let (tradeCondition2, bytes) ← TradeCondition2.decode bytes
  let (tradeCondition3, bytes) ← TradeCondition3.decode bytes
  let (tradeCondition4, bytes) ← TradeCondition4.decode bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNumber, originalTradeId, tradeId, price, volume, tradeCondition1, tradeCondition2, tradeCondition3, tradeCondition4, marketId }, bytes)

@[simp] theorem encode_length (message : ConsolidatedTradeCorrectionMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCondition1.encode_length, TradeCondition2.encode_length, TradeCondition3.encode_length, TradeCondition4.encode_length]

theorem encode_length_pos (message : ConsolidatedTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedTradeCorrectionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeCondition1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCondition2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCondition3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCondition4.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConsolidatedTradeCorrectionMessage

/-- Trf Fractional Prior Day Trade Message: 44 bytes -/
structure TrfFractionalPriorDayTradeMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  fractionalVolume : BitVec 64
  tradeCond1 : TradeCond1
  tradeCond2 : TradeCond2
  tradeCond3 : TradeCond3
  tradeCond4 : TradeCond4
  priorDayTime : BitVec 32
  priorDayTimeNs : BitVec 32
  deriving DecidableEq, Repr

namespace TrfFractionalPriorDayTradeMessage

def encode (message : TrfFractionalPriorDayTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 8 message.fractionalVolume
    ++ (TradeCond1.encode message.tradeCond1
    ++ (TradeCond2.encode message.tradeCond2
    ++ (TradeCond3.encode message.tradeCond3
    ++ (TradeCond4.encode message.tradeCond4
    ++ (encodeUIntLE 4 message.priorDayTime
    ++ (encodeUIntLE 4 message.priorDayTimeNs))))))))))))

def decode (bytes : List UInt8) : Option (TrfFractionalPriorDayTradeMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (fractionalVolume, bytes) ← decodeUIntLE 8 bytes
  let (tradeCond1, bytes) ← TradeCond1.decode bytes
  let (tradeCond2, bytes) ← TradeCond2.decode bytes
  let (tradeCond3, bytes) ← TradeCond3.decode bytes
  let (tradeCond4, bytes) ← TradeCond4.decode bytes
  let (priorDayTime, bytes) ← decodeUIntLE 4 bytes
  let (priorDayTimeNs, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, tradeId, price, fractionalVolume, tradeCond1, tradeCond2, tradeCond3, tradeCond4, priorDayTime, priorDayTimeNs }, bytes)

@[simp] theorem encode_length (message : TrfFractionalPriorDayTradeMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCond1.encode_length, TradeCond2.encode_length, TradeCond3.encode_length, TradeCond4.encode_length]

theorem encode_length_pos (message : TrfFractionalPriorDayTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TrfFractionalPriorDayTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeCond1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCond2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCond3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCond4.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TrfFractionalPriorDayTradeMessage

/-- Trf Fractional Prior Day Trade Cancel Message: 40 bytes -/
structure TrfFractionalPriorDayTradeCancelMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  fractionalVolume : BitVec 64
  priorDayTime : BitVec 32
  priorDayTimeNs : BitVec 32
  deriving DecidableEq, Repr

namespace TrfFractionalPriorDayTradeCancelMessage

def encode (message : TrfFractionalPriorDayTradeCancelMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 8 message.fractionalVolume
    ++ (encodeUIntLE 4 message.priorDayTime
    ++ (encodeUIntLE 4 message.priorDayTimeNs))))))))

def decode (bytes : List UInt8) : Option (TrfFractionalPriorDayTradeCancelMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (fractionalVolume, bytes) ← decodeUIntLE 8 bytes
  let (priorDayTime, bytes) ← decodeUIntLE 4 bytes
  let (priorDayTimeNs, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, tradeId, price, fractionalVolume, priorDayTime, priorDayTimeNs }, bytes)

@[simp] theorem encode_length (message : TrfFractionalPriorDayTradeCancelMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TrfFractionalPriorDayTradeCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TrfFractionalPriorDayTradeCancelMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TrfFractionalPriorDayTradeCancelMessage

/-- Consolidated Fractional Stock Summary Message: 62 bytes -/
structure ConsolidatedFractionalStockSummaryMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  nyseGroupHighPrice : BitVec 32
  nyseGroupLowPrice : BitVec 32
  primaryListingMarketOfficialOpenPrice : BitVec 32
  fractionalNyseGroupVolume : BitVec 64
  nyseGroupMarketIdOfHighPrice : BitVec 16
  nyseGroupMarketIdOfLowPrice : BitVec 16
  marketIdOfOpenPrice : BitVec 16
  numClosePrices : BitVec 8
  nyseGroupMarketIdOfTheClose : BitVec 16
  primaryListingMarketOfficialClosePrice : BitVec 32
  consolidatedHighPrice : BitVec 32
  consolidatedLowPrice : BitVec 32
  consolidatedFirstPrice : BitVec 32
  consolidatedLastPrice : BitVec 32
  complete : BitVec 8
  deriving DecidableEq, Repr

namespace ConsolidatedFractionalStockSummaryMessage

def encode (message : ConsolidatedFractionalStockSummaryMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.nyseGroupHighPrice
    ++ (encodeUIntLE 4 message.nyseGroupLowPrice
    ++ (encodeUIntLE 4 message.primaryListingMarketOfficialOpenPrice
    ++ (encodeUIntLE 8 message.fractionalNyseGroupVolume
    ++ (encodeUIntLE 2 message.nyseGroupMarketIdOfHighPrice
    ++ (encodeUIntLE 2 message.nyseGroupMarketIdOfLowPrice
    ++ (encodeUIntLE 2 message.marketIdOfOpenPrice
    ++ (encodeUIntLE 1 message.numClosePrices
    ++ (encodeUIntLE 2 message.nyseGroupMarketIdOfTheClose
    ++ (encodeUIntLE 4 message.primaryListingMarketOfficialClosePrice
    ++ (encodeUIntLE 4 message.consolidatedHighPrice
    ++ (encodeUIntLE 4 message.consolidatedLowPrice
    ++ (encodeUIntLE 4 message.consolidatedFirstPrice
    ++ (encodeUIntLE 4 message.consolidatedLastPrice
    ++ (encodeUIntLE 1 message.complete)))))))))))))))))

def decode (bytes : List UInt8) : Option (ConsolidatedFractionalStockSummaryMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (nyseGroupHighPrice, bytes) ← decodeUIntLE 4 bytes
  let (nyseGroupLowPrice, bytes) ← decodeUIntLE 4 bytes
  let (primaryListingMarketOfficialOpenPrice, bytes) ← decodeUIntLE 4 bytes
  let (fractionalNyseGroupVolume, bytes) ← decodeUIntLE 8 bytes
  let (nyseGroupMarketIdOfHighPrice, bytes) ← decodeUIntLE 2 bytes
  let (nyseGroupMarketIdOfLowPrice, bytes) ← decodeUIntLE 2 bytes
  let (marketIdOfOpenPrice, bytes) ← decodeUIntLE 2 bytes
  let (numClosePrices, bytes) ← decodeUIntLE 1 bytes
  let (nyseGroupMarketIdOfTheClose, bytes) ← decodeUIntLE 2 bytes
  let (primaryListingMarketOfficialClosePrice, bytes) ← decodeUIntLE 4 bytes
  let (consolidatedHighPrice, bytes) ← decodeUIntLE 4 bytes
  let (consolidatedLowPrice, bytes) ← decodeUIntLE 4 bytes
  let (consolidatedFirstPrice, bytes) ← decodeUIntLE 4 bytes
  let (consolidatedLastPrice, bytes) ← decodeUIntLE 4 bytes
  let (complete, bytes) ← decodeUIntLE 1 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, nyseGroupHighPrice, nyseGroupLowPrice, primaryListingMarketOfficialOpenPrice, fractionalNyseGroupVolume, nyseGroupMarketIdOfHighPrice, nyseGroupMarketIdOfLowPrice, marketIdOfOpenPrice, numClosePrices, nyseGroupMarketIdOfTheClose, primaryListingMarketOfficialClosePrice, consolidatedHighPrice, consolidatedLowPrice, consolidatedFirstPrice, consolidatedLastPrice, complete }, bytes)

@[simp] theorem encode_length (message : ConsolidatedFractionalStockSummaryMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ConsolidatedFractionalStockSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedFractionalStockSummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConsolidatedFractionalStockSummaryMessage

/-- Consolidated Fractional Volume Message: 18 bytes -/
structure ConsolidatedFractionalVolumeMessage where
  symbolIndex : BitVec 32
  symbolSeqNumber : BitVec 32
  fractionalConsolidatedVolume : BitVec 64
  reason : BitVec 8
  complete : BitVec 8
  deriving DecidableEq, Repr

namespace ConsolidatedFractionalVolumeMessage

def encode (message : ConsolidatedFractionalVolumeMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNumber
    ++ (encodeUIntLE 8 message.fractionalConsolidatedVolume
    ++ (encodeUIntLE 1 message.reason
    ++ (encodeUIntLE 1 message.complete))))

def decode (bytes : List UInt8) : Option (ConsolidatedFractionalVolumeMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNumber, bytes) ← decodeUIntLE 4 bytes
  let (fractionalConsolidatedVolume, bytes) ← decodeUIntLE 8 bytes
  let (reason, bytes) ← decodeUIntLE 1 bytes
  let (complete, bytes) ← decodeUIntLE 1 bytes
  pure ({ symbolIndex, symbolSeqNumber, fractionalConsolidatedVolume, reason, complete }, bytes)

@[simp] theorem encode_length (message : ConsolidatedFractionalVolumeMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ConsolidatedFractionalVolumeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedFractionalVolumeMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConsolidatedFractionalVolumeMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | sequenceNumberResetMessage (message : SequenceNumberResetMessage) -- 1
  | sourceTimeReferenceMessage (message : SourceTimeReferenceMessage) -- 2
  | symbolIndexMappingMessage (message : SymbolIndexMappingMessage) -- 3
  | symbolClearMessage (message : SymbolClearMessage) -- 32
  | securityStatusMessage (message : SecurityStatusMessage) -- 34
  | retransmissionRequestMessage (message : RetransmissionRequestMessage) -- 10
  | symbolIndexMappingRequestMessage (message : SymbolIndexMappingRequestMessage) -- 13
  | refreshRequestMessage (message : RefreshRequestMessage) -- 15
  | messageUnavailableMessage (message : MessageUnavailableMessage) -- 31
  | refreshHeaderMessage (message : RefreshHeaderMessage) -- 35
  | requestResponseMessage (message : RequestResponseMessage) -- 11
  | heartbeatResponseMessage (message : HeartbeatResponseMessage) -- 12
  | bestQuotesMessage (message : BestQuotesMessage) -- 142
  | consolidatedSingleSidedQuoteMessage (message : ConsolidatedSingleSidedQuoteMessage) -- 143
  | trfFractionalTradeMessage (message : TrfFractionalTradeMessage) -- 210
  | consolidatedTradeMessage (message : ConsolidatedTradeMessage) -- 220
  | consolidatedTradeCancelMessage (message : ConsolidatedTradeCancelMessage) -- 221
  | trfFractionalTradeCorrectionMessage (message : TrfFractionalTradeCorrectionMessage) -- 212
  | consolidatedTradeCorrectionMessage (message : ConsolidatedTradeCorrectionMessage) -- 222
  | trfFractionalPriorDayTradeMessage (message : TrfFractionalPriorDayTradeMessage) -- 213
  | trfFractionalPriorDayTradeCancelMessage (message : TrfFractionalPriorDayTradeCancelMessage) -- 214
  | consolidatedFractionalStockSummaryMessage (message : ConsolidatedFractionalStockSummaryMessage) -- 202
  | consolidatedFractionalVolumeMessage (message : ConsolidatedFractionalVolumeMessage) -- 201
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceNumberResetMessage _ => 1
  | .sourceTimeReferenceMessage _ => 2
  | .symbolIndexMappingMessage _ => 3
  | .symbolClearMessage _ => 32
  | .securityStatusMessage _ => 34
  | .retransmissionRequestMessage _ => 10
  | .symbolIndexMappingRequestMessage _ => 13
  | .refreshRequestMessage _ => 15
  | .messageUnavailableMessage _ => 31
  | .refreshHeaderMessage _ => 35
  | .requestResponseMessage _ => 11
  | .heartbeatResponseMessage _ => 12
  | .bestQuotesMessage _ => 142
  | .consolidatedSingleSidedQuoteMessage _ => 143
  | .trfFractionalTradeMessage _ => 210
  | .consolidatedTradeMessage _ => 220
  | .consolidatedTradeCancelMessage _ => 221
  | .trfFractionalTradeCorrectionMessage _ => 212
  | .consolidatedTradeCorrectionMessage _ => 222
  | .trfFractionalPriorDayTradeMessage _ => 213
  | .trfFractionalPriorDayTradeCancelMessage _ => 214
  | .consolidatedFractionalStockSummaryMessage _ => 202
  | .consolidatedFractionalVolumeMessage _ => 201

def encode : Payload → List UInt8
  | .sequenceNumberResetMessage message => SequenceNumberResetMessage.encode message
  | .sourceTimeReferenceMessage message => SourceTimeReferenceMessage.encode message
  | .symbolIndexMappingMessage message => SymbolIndexMappingMessage.encode message
  | .symbolClearMessage message => SymbolClearMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .retransmissionRequestMessage message => RetransmissionRequestMessage.encode message
  | .symbolIndexMappingRequestMessage message => SymbolIndexMappingRequestMessage.encode message
  | .refreshRequestMessage message => RefreshRequestMessage.encode message
  | .messageUnavailableMessage message => MessageUnavailableMessage.encode message
  | .refreshHeaderMessage message => RefreshHeaderMessage.encode message
  | .requestResponseMessage message => RequestResponseMessage.encode message
  | .heartbeatResponseMessage message => HeartbeatResponseMessage.encode message
  | .bestQuotesMessage message => BestQuotesMessage.encode message
  | .consolidatedSingleSidedQuoteMessage message => ConsolidatedSingleSidedQuoteMessage.encode message
  | .trfFractionalTradeMessage message => TrfFractionalTradeMessage.encode message
  | .consolidatedTradeMessage message => ConsolidatedTradeMessage.encode message
  | .consolidatedTradeCancelMessage message => ConsolidatedTradeCancelMessage.encode message
  | .trfFractionalTradeCorrectionMessage message => TrfFractionalTradeCorrectionMessage.encode message
  | .consolidatedTradeCorrectionMessage message => ConsolidatedTradeCorrectionMessage.encode message
  | .trfFractionalPriorDayTradeMessage message => TrfFractionalPriorDayTradeMessage.encode message
  | .trfFractionalPriorDayTradeCancelMessage message => TrfFractionalPriorDayTradeCancelMessage.encode message
  | .consolidatedFractionalStockSummaryMessage message => ConsolidatedFractionalStockSummaryMessage.encode message
  | .consolidatedFractionalVolumeMessage message => ConsolidatedFractionalVolumeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 62 := by
  cases message with
  | sequenceNumberResetMessage inner =>
    simp only [encode, SequenceNumberResetMessage.encode_length]
    omega
  | sourceTimeReferenceMessage inner =>
    simp only [encode, SourceTimeReferenceMessage.encode_length]
    omega
  | symbolIndexMappingMessage inner =>
    simp only [encode, SymbolIndexMappingMessage.encode_length]
    omega
  | symbolClearMessage inner =>
    simp only [encode, SymbolClearMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [encode, RetransmissionRequestMessage.encode_length]
    omega
  | symbolIndexMappingRequestMessage inner =>
    simp only [encode, SymbolIndexMappingRequestMessage.encode_length]
    omega
  | refreshRequestMessage inner =>
    simp only [encode, RefreshRequestMessage.encode_length]
    omega
  | messageUnavailableMessage inner =>
    simp only [encode, MessageUnavailableMessage.encode_length]
    omega
  | refreshHeaderMessage inner =>
    have bound_inner := RefreshHeaderMessage.encode_length_le inner
    simp only [encode]
    omega
  | requestResponseMessage inner =>
    simp only [encode, RequestResponseMessage.encode_length]
    omega
  | heartbeatResponseMessage inner =>
    simp only [encode, HeartbeatResponseMessage.encode_length]
    omega
  | bestQuotesMessage inner =>
    simp only [encode, BestQuotesMessage.encode_length]
    omega
  | consolidatedSingleSidedQuoteMessage inner =>
    simp only [encode, ConsolidatedSingleSidedQuoteMessage.encode_length]
    omega
  | trfFractionalTradeMessage inner =>
    simp only [encode, TrfFractionalTradeMessage.encode_length]
    omega
  | consolidatedTradeMessage inner =>
    simp only [encode, ConsolidatedTradeMessage.encode_length]
    omega
  | consolidatedTradeCancelMessage inner =>
    simp only [encode, ConsolidatedTradeCancelMessage.encode_length]
    omega
  | trfFractionalTradeCorrectionMessage inner =>
    simp only [encode, TrfFractionalTradeCorrectionMessage.encode_length]
    omega
  | consolidatedTradeCorrectionMessage inner =>
    simp only [encode, ConsolidatedTradeCorrectionMessage.encode_length]
    omega
  | trfFractionalPriorDayTradeMessage inner =>
    simp only [encode, TrfFractionalPriorDayTradeMessage.encode_length]
    omega
  | trfFractionalPriorDayTradeCancelMessage inner =>
    simp only [encode, TrfFractionalPriorDayTradeCancelMessage.encode_length]
    omega
  | consolidatedFractionalStockSummaryMessage inner =>
    simp only [encode, ConsolidatedFractionalStockSummaryMessage.encode_length]
    omega
  | consolidatedFractionalVolumeMessage inner =>
    simp only [encode, ConsolidatedFractionalVolumeMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (SequenceNumberResetMessage.decode bytes).map fun (message, rest) => (.sequenceNumberResetMessage message, rest)
  else if tag = 2 then (SourceTimeReferenceMessage.decode bytes).map fun (message, rest) => (.sourceTimeReferenceMessage message, rest)
  else if tag = 3 then (SymbolIndexMappingMessage.decode bytes).map fun (message, rest) => (.symbolIndexMappingMessage message, rest)
  else if tag = 32 then (SymbolClearMessage.decode bytes).map fun (message, rest) => (.symbolClearMessage message, rest)
  else if tag = 34 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 10 then (RetransmissionRequestMessage.decode bytes).map fun (message, rest) => (.retransmissionRequestMessage message, rest)
  else if tag = 13 then (SymbolIndexMappingRequestMessage.decode bytes).map fun (message, rest) => (.symbolIndexMappingRequestMessage message, rest)
  else if tag = 15 then (RefreshRequestMessage.decode bytes).map fun (message, rest) => (.refreshRequestMessage message, rest)
  else if tag = 31 then (MessageUnavailableMessage.decode bytes).map fun (message, rest) => (.messageUnavailableMessage message, rest)
  else if tag = 35 then (RefreshHeaderMessage.decode bytes).map fun (message, rest) => (.refreshHeaderMessage message, rest)
  else if tag = 11 then (RequestResponseMessage.decode bytes).map fun (message, rest) => (.requestResponseMessage message, rest)
  else if tag = 12 then (HeartbeatResponseMessage.decode bytes).map fun (message, rest) => (.heartbeatResponseMessage message, rest)
  else if tag = 142 then (BestQuotesMessage.decode bytes).map fun (message, rest) => (.bestQuotesMessage message, rest)
  else if tag = 143 then (ConsolidatedSingleSidedQuoteMessage.decode bytes).map fun (message, rest) => (.consolidatedSingleSidedQuoteMessage message, rest)
  else if tag = 210 then (TrfFractionalTradeMessage.decode bytes).map fun (message, rest) => (.trfFractionalTradeMessage message, rest)
  else if tag = 220 then (ConsolidatedTradeMessage.decode bytes).map fun (message, rest) => (.consolidatedTradeMessage message, rest)
  else if tag = 221 then (ConsolidatedTradeCancelMessage.decode bytes).map fun (message, rest) => (.consolidatedTradeCancelMessage message, rest)
  else if tag = 212 then (TrfFractionalTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.trfFractionalTradeCorrectionMessage message, rest)
  else if tag = 222 then (ConsolidatedTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.consolidatedTradeCorrectionMessage message, rest)
  else if tag = 213 then (TrfFractionalPriorDayTradeMessage.decode bytes).map fun (message, rest) => (.trfFractionalPriorDayTradeMessage message, rest)
  else if tag = 214 then (TrfFractionalPriorDayTradeCancelMessage.decode bytes).map fun (message, rest) => (.trfFractionalPriorDayTradeCancelMessage message, rest)
  else if tag = 202 then (ConsolidatedFractionalStockSummaryMessage.decode bytes).map fun (message, rest) => (.consolidatedFractionalStockSummaryMessage message, rest)
  else if tag = 201 then (ConsolidatedFractionalVolumeMessage.decode bytes).map fun (message, rest) => (.consolidatedFractionalVolumeMessage message, rest)
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
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | sequenceNumberResetMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SequenceNumberResetMessage.encode_length]
    omega
  | sourceTimeReferenceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SourceTimeReferenceMessage.encode_length]
    omega
  | symbolIndexMappingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SymbolIndexMappingMessage.encode_length]
    omega
  | symbolClearMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SymbolClearMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SecurityStatusMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RetransmissionRequestMessage.encode_length]
    omega
  | symbolIndexMappingRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SymbolIndexMappingRequestMessage.encode_length]
    omega
  | refreshRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RefreshRequestMessage.encode_length]
    omega
  | messageUnavailableMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, MessageUnavailableMessage.encode_length]
    omega
  | refreshHeaderMessage inner =>
    have bound_inner := RefreshHeaderMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | requestResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RequestResponseMessage.encode_length]
    omega
  | heartbeatResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, HeartbeatResponseMessage.encode_length]
    omega
  | bestQuotesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, BestQuotesMessage.encode_length]
    omega
  | consolidatedSingleSidedQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedSingleSidedQuoteMessage.encode_length]
    omega
  | trfFractionalTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TrfFractionalTradeMessage.encode_length]
    omega
  | consolidatedTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedTradeMessage.encode_length]
    omega
  | consolidatedTradeCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedTradeCancelMessage.encode_length]
    omega
  | trfFractionalTradeCorrectionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TrfFractionalTradeCorrectionMessage.encode_length]
    omega
  | consolidatedTradeCorrectionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedTradeCorrectionMessage.encode_length]
    omega
  | trfFractionalPriorDayTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TrfFractionalPriorDayTradeMessage.encode_length]
    omega
  | trfFractionalPriorDayTradeCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TrfFractionalPriorDayTradeCancelMessage.encode_length]
    omega
  | consolidatedFractionalStockSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedFractionalStockSummaryMessage.encode_length]
    omega
  | consolidatedFractionalVolumeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedFractionalVolumeMessage.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  packetSize : BitVec 16
  deliveryFlag : BitVec 8
  sequenceNumber : BitVec 32
  sendTime : SendTime
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.packetSize
    ++ (encodeUIntLE 1 message.deliveryFlag
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (SendTime.encode message.sendTime
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (packetSize, bytes) ← decodeUIntLE 2 bytes
  let (deliveryFlag, bytes) ← decodeUIntLE 1 bytes
  let (messageCount, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← SendTime.decode bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ packetSize, deliveryFlag, sequenceNumber, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
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
  rw [List.append_assoc, SendTime.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NyseAmexequitiesBqtXdpV24A
