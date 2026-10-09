import Wire

/-!
# New York Stock Exchange Deep Feed v1.2.m

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseArcaoptionsDeepfeedPillarV12M

/-- Exchange Code: one byte code -/
def ExchangeCode.codes : List UInt8 :=
  [0x41, 0x46, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x56, 0x5A, 0x20]

inductive ExchangeCode where
  | nyseAmerican -- Nyse American
  | txse -- Txse
  | ltse -- Ltse
  | nyseTexas -- Nyse Texas
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | iex -- Iex
  | cboe -- Cboe
  | otcOrIndexBasedProductSpaceOr0X20 -- Otc Or Index Based Product Space Or 0 X 20
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeCode

def toByte : ExchangeCode → UInt8
  | .nyseAmerican => 0x41
  | .txse => 0x46
  | .ltse => 0x4C
  | .nyseTexas => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .iex => 0x56
  | .cboe => 0x5A
  | .otcOrIndexBasedProductSpaceOr0X20 => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExchangeCode :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x46 then .txse
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x56 then .iex
  else if byte = 0x5A then .cboe
  else .otcOrIndexBasedProductSpaceOr0X20

def ofByte (byte : UInt8) : ExchangeCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeCode) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | txse => decide
  | ltse => decide
  | nyseTexas => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | iex => decide
  | cboe => decide
  | otcOrIndexBasedProductSpaceOr0X20 => decide
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
  | americanDepositaryReceipts -- American Depositary Receipts
  | commonStock -- Common Stock
  | debentures -- Debentures
  | exchangeTradedFunds -- Exchange Traded Funds
  | foreign -- Foreign
  | americanDepositaryShares -- American Depositary Shares
  | units -- Units
  | indexLinkedNotes -- Index Linked Notes
  | otherBlank -- Other Blank
  | ordinaryShares -- Ordinary Shares
  | preferredStock -- Preferred Stock
  | rights -- Rights
  | sharesOfBeneficialInterest -- Shares Of Beneficial Interest
  | test -- Test
  | closedEndFund -- Closed End Fund
  | warrants -- Warrants
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityType

def toByte : SecurityType → UInt8
  | .americanDepositaryReceipts => 0x41
  | .commonStock => 0x43
  | .debentures => 0x44
  | .exchangeTradedFunds => 0x45
  | .foreign => 0x46
  | .americanDepositaryShares => 0x48
  | .units => 0x49
  | .indexLinkedNotes => 0x4C
  | .otherBlank => 0x4D
  | .ordinaryShares => 0x4F
  | .preferredStock => 0x50
  | .rights => 0x52
  | .sharesOfBeneficialInterest => 0x53
  | .test => 0x54
  | .closedEndFund => 0x55
  | .warrants => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityType :=
  if byte = 0x41 then .americanDepositaryReceipts
  else if byte = 0x43 then .commonStock
  else if byte = 0x44 then .debentures
  else if byte = 0x45 then .exchangeTradedFunds
  else if byte = 0x46 then .foreign
  else if byte = 0x48 then .americanDepositaryShares
  else if byte = 0x49 then .units
  else if byte = 0x4C then .indexLinkedNotes
  else if byte = 0x4D then .otherBlank
  else if byte = 0x4F then .ordinaryShares
  else if byte = 0x50 then .preferredStock
  else if byte = 0x52 then .rights
  else if byte = 0x53 then .sharesOfBeneficialInterest
  else if byte = 0x54 then .test
  else if byte = 0x55 then .closedEndFund
  else .warrants

def ofByte (byte : UInt8) : SecurityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityType) : ofByte value.toByte = value := by
  cases value with
  | americanDepositaryReceipts => decide
  | commonStock => decide
  | debentures => decide
  | exchangeTradedFunds => decide
  | foreign => decide
  | americanDepositaryShares => decide
  | units => decide
  | indexLinkedNotes => decide
  | otherBlank => decide
  | ordinaryShares => decide
  | preferredStock => decide
  | rights => decide
  | sharesOfBeneficialInterest => decide
  | test => decide
  | closedEndFund => decide
  | warrants => decide
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
  | lateSession -- Late Session
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
  | .lateSession => 0x4C
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
  else if byte = 0x4C then .lateSession
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
  | lateSession => decide
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
  | newsReleased -- News Released
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
  | .newsReleased => 0x44
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
  else if byte = 0x44 then .newsReleased
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
  | newsReleased => decide
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
  [0x41, 0x42, 0x43, 0x44, 0x47, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x53, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x48, 0x55, 0x20]

inductive SsrTriggeringExchangeId where
  | nyseAmerican -- Nyse American
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nyseNational -- Nyse National
  | finra -- Finra
  | n24X -- N 24 X
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseTexas -- Nyse Texas
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | cts -- Cts
  | nasdaqOmx -- Nasdaq Omx
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqOmxPsx -- Nasdaq Omx Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | miax -- Miax
  | memx -- Memx
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
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseTexas => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .cts => 0x53
  | .nasdaqOmx => 0x54
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqOmxPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .miax => 0x48
  | .memx => 0x55
  | .noValue => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SsrTriggeringExchangeId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqOmxBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finra
  else if byte = 0x47 then .n24X
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x53 then .cts
  else if byte = 0x54 then .nasdaqOmx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqOmxPsx
  else if byte = 0x59 then .cboeByx
  else if byte = 0x5A then .cboeBzx
  else if byte = 0x48 then .miax
  else if byte = 0x55 then .memx
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
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseTexas => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | cts => decide
  | nasdaqOmx => decide
  | iex => decide
  | cbsx => decide
  | nasdaqOmxPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | miax => decide
  | memx => decide
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

/-- Closing Only Indicator: one byte code -/
def ClosingOnlyIndicator.codes : List UInt8 :=
  [0x30, 0x31]

inductive ClosingOnlyIndicator where
  | standardSeries -- Standard Series
  | closingOnlySeries -- Closing Only Series
  | unlisted (byte : { byte : UInt8 // byte ∉ ClosingOnlyIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClosingOnlyIndicator

def toByte : ClosingOnlyIndicator → UInt8
  | .standardSeries => 0x30
  | .closingOnlySeries => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClosingOnlyIndicator :=
  if byte = 0x30 then .standardSeries
  else .closingOnlySeries

def ofByte (byte : UInt8) : ClosingOnlyIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClosingOnlyIndicator) : ofByte value.toByte = value := by
  cases value with
  | standardSeries => decide
  | closingOnlySeries => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClosingOnlyIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClosingOnlyIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClosingOnlyIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ClosingOnlyIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClosingOnlyIndicator

/-- Series Status: one byte code -/
def SeriesStatus.codes : List UInt8 :=
  [0x34, 0x35, 0x36, 0x50, 0x42, 0x4F, 0x58]

inductive SeriesStatus where
  | tradingHalt -- Trading Halt
  | resume -- Resume
  | suspend -- Suspend
  | preopening -- Preopening
  | beginAcceptingOrders -- Begin Accepting Orders
  | coreSession -- Core Session
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ SeriesStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SeriesStatus

def toByte : SeriesStatus → UInt8
  | .tradingHalt => 0x34
  | .resume => 0x35
  | .suspend => 0x36
  | .preopening => 0x50
  | .beginAcceptingOrders => 0x42
  | .coreSession => 0x4F
  | .closed => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SeriesStatus :=
  if byte = 0x34 then .tradingHalt
  else if byte = 0x35 then .resume
  else if byte = 0x36 then .suspend
  else if byte = 0x50 then .preopening
  else if byte = 0x42 then .beginAcceptingOrders
  else if byte = 0x4F then .coreSession
  else .closed

def ofByte (byte : UInt8) : SeriesStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SeriesStatus) : ofByte value.toByte = value := by
  cases value with
  | tradingHalt => decide
  | resume => decide
  | suspend => decide
  | preopening => decide
  | beginAcceptingOrders => decide
  | coreSession => decide
  | closed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SeriesStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SeriesStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SeriesStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SeriesStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SeriesStatus

/-- Options Status Halt Condition: one byte code -/
def OptionsStatusHaltCondition.codes : List UInt8 :=
  [0x7E, 0x68]

inductive OptionsStatusHaltCondition where
  | seriesNotDelayedhalted -- Series Not Delayedhalted
  | optionSeriesIsHalted -- Option Series Is Halted
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionsStatusHaltCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionsStatusHaltCondition

def toByte : OptionsStatusHaltCondition → UInt8
  | .seriesNotDelayedhalted => 0x7E
  | .optionSeriesIsHalted => 0x68
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionsStatusHaltCondition :=
  if byte = 0x7E then .seriesNotDelayedhalted
  else .optionSeriesIsHalted

def ofByte (byte : UInt8) : OptionsStatusHaltCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionsStatusHaltCondition) : ofByte value.toByte = value := by
  cases value with
  | seriesNotDelayedhalted => decide
  | optionSeriesIsHalted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionsStatusHaltCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionsStatusHaltCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionsStatusHaltCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionsStatusHaltCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionsStatusHaltCondition

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

/-- Leg Security Type: one byte code -/
def LegSecurityType.codes : List UInt8 :=
  [0x4F, 0x45, 0x46]

inductive LegSecurityType where
  | optionsSeriesLeg -- Options Series Leg
  | equityStockLeg -- Equity Stock Leg
  | optionsFlexLeg -- Options Flex Leg
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSecurityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSecurityType

def toByte : LegSecurityType → UInt8
  | .optionsSeriesLeg => 0x4F
  | .equityStockLeg => 0x45
  | .optionsFlexLeg => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSecurityType :=
  if byte = 0x4F then .optionsSeriesLeg
  else if byte = 0x45 then .equityStockLeg
  else .optionsFlexLeg

def ofByte (byte : UInt8) : LegSecurityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSecurityType) : ofByte value.toByte = value := by
  cases value with
  | optionsSeriesLeg => decide
  | equityStockLeg => decide
  | optionsFlexLeg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSecurityType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSecurityType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSecurityType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegSecurityType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSecurityType

/-- Status: one byte code -/
def Status.codes : List UInt8 :=
  [0x30, 0x31, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]

inductive Status where
  | messageWasAccepted -- Message Was Accepted
  | rejectedDueToAnInvalidSourceId -- Rejected Due To An Invalid Source Id
  | rejectedDueToMaximumSequenceRange -- Rejected Due To Maximum Sequence Range
  | rejectedDueToMaximumRequestInADay -- Rejected Due To Maximum Request In A Day
  | rejectedDueToMaximumNumberOfRefreshRequestsInADay -- Rejected Due To Maximum Number Of Refresh Requests In A Day
  | rejectedRequestMessageSeqNumTtlIsTooOld -- Rejected Request Message Seq Num Ttl Is Too Old
  | rejectedDueToAnInvalidChannelId -- Rejected Due To An Invalid Channel Id
  | rejectedDueToAnInvalidProductId -- Rejected Due To An Invalid Product Id
  | rejectedDueToInvalidMsgTypeOrMismatchBetweenMsgTypeAndMsgSize -- Rejected Due To Invalid Msg Type Or Mismatch Between Msg Type And Msg Size
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .messageWasAccepted => 0x30
  | .rejectedDueToAnInvalidSourceId => 0x31
  | .rejectedDueToMaximumSequenceRange => 0x33
  | .rejectedDueToMaximumRequestInADay => 0x34
  | .rejectedDueToMaximumNumberOfRefreshRequestsInADay => 0x35
  | .rejectedRequestMessageSeqNumTtlIsTooOld => 0x36
  | .rejectedDueToAnInvalidChannelId => 0x37
  | .rejectedDueToAnInvalidProductId => 0x38
  | .rejectedDueToInvalidMsgTypeOrMismatchBetweenMsgTypeAndMsgSize => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x30 then .messageWasAccepted
  else if byte = 0x31 then .rejectedDueToAnInvalidSourceId
  else if byte = 0x33 then .rejectedDueToMaximumSequenceRange
  else if byte = 0x34 then .rejectedDueToMaximumRequestInADay
  else if byte = 0x35 then .rejectedDueToMaximumNumberOfRefreshRequestsInADay
  else if byte = 0x36 then .rejectedRequestMessageSeqNumTtlIsTooOld
  else if byte = 0x37 then .rejectedDueToAnInvalidChannelId
  else if byte = 0x38 then .rejectedDueToAnInvalidProductId
  else .rejectedDueToInvalidMsgTypeOrMismatchBetweenMsgTypeAndMsgSize

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | messageWasAccepted => decide
  | rejectedDueToAnInvalidSourceId => decide
  | rejectedDueToMaximumSequenceRange => decide
  | rejectedDueToMaximumRequestInADay => decide
  | rejectedDueToMaximumNumberOfRefreshRequestsInADay => decide
  | rejectedRequestMessageSeqNumTtlIsTooOld => decide
  | rejectedDueToAnInvalidChannelId => decide
  | rejectedDueToAnInvalidProductId => decide
  | rejectedDueToInvalidMsgTypeOrMismatchBetweenMsgTypeAndMsgSize => decide
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

/-- Cust Indicator: one byte code -/
def CustIndicator.codes : List UInt8 :=
  [0x43, 0x4E, 0x44]

inductive CustIndicator where
  | customer -- Customer
  | noncustomer -- Noncustomer
  | derivedForFutureUse -- Derived For Future Use
  | unlisted (byte : { byte : UInt8 // byte ∉ CustIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CustIndicator

def toByte : CustIndicator → UInt8
  | .customer => 0x43
  | .noncustomer => 0x4E
  | .derivedForFutureUse => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CustIndicator :=
  if byte = 0x43 then .customer
  else if byte = 0x4E then .noncustomer
  else .derivedForFutureUse

def ofByte (byte : UInt8) : CustIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CustIndicator) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | noncustomer => decide
  | derivedForFutureUse => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CustIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CustIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CustIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CustIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CustIndicator

/-- Trade Cond 1: one byte code -/
def TradeCond1.codes : List UInt8 :=
  [0x61, 0x63, 0x65, 0x49, 0x53, 0x44, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6D, 0x70, 0x73, 0x76]

inductive TradeCond1 where
  | outrightSeriesOrderquoteTradingElectronicallyWithAOutrightSeriesCubeOrderOrOutrightSeriesCubeOrderTradingElectronicallyWithOutrightSeriesCubeContraOrder -- Outright Series Orderquote Trading Electronically With A Outright Series Cube Order Or Outright Series Cube Order Trading Electronically With Outright Series Cube Contra Order
  | tradingOfAnOutrightSeriesQccOrderOrCustomerToCustomerCrossOrder -- Trading Of An Outright Series Qcc Order Or Customer To Customer Cross Order
  | outrightSeriesFloorTrade -- Outright Series Floor Trade
  | allOutrightSeriesElectronicTradesExcludingAwayMarketExecutionsThatWereNotPartOfCertainTransactions -- All Outright Series Electronic Trades Excluding Away Market Executions That Were Not Part Of Certain Transactions
  | allOutrightSeriesTradesGeneratedAsPartOfAnIntermarketSweepOrder -- All Outright Series Trades Generated As Part Of An Intermarket Sweep Order
  | transactionIsBeingReportedLateButIsInTheCorrectSequence -- Transaction Is Being Reported Late But Is In The Correct Sequence
  | complexOrderTradesThatWereNotPartOfCertainTransactions -- Complex Order Trades That Were Not Part Of Certain Transactions
  | complexOrderTradingElectronicallyWithAComplexCubeOrderOrComplexCubeOrderTradingElectronicallyWithComplexCubeContraOrder -- Complex Order Trading Electronically With A Complex Cube Order Or Complex Cube Order Trading Electronically With Complex Cube Contra Order
  | tradingOfAComplexQccOrderOrCustomerToCustomerCrossOrder -- Trading Of A Complex Qcc Order Or Customer To Customer Cross Order
  | complexOrderToComplexOrderFloorTrade -- Complex Order To Complex Order Floor Trade
  | complexOrderTradingElectronicallyWithTheOutrightSeriesOrdersquotes -- Complex Order Trading Electronically With The Outright Series Ordersquotes
  | complexOrderToOutrightSeriesOrderFloorTrade -- Complex Order To Outright Series Order Floor Trade
  | complexOrderWithStockToComplexOrderWithStockFloorTrade -- Complex Order With Stock To Complex Order With Stock Floor Trade
  | complexOrderWithStockToOutrightSeriesOrderFloorTrade -- Complex Order With Stock To Outright Series Order Floor Trade
  | extendedHoursTrade -- Extended Hours Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCond1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCond1

def toByte : TradeCond1 → UInt8
  | .outrightSeriesOrderquoteTradingElectronicallyWithAOutrightSeriesCubeOrderOrOutrightSeriesCubeOrderTradingElectronicallyWithOutrightSeriesCubeContraOrder => 0x61
  | .tradingOfAnOutrightSeriesQccOrderOrCustomerToCustomerCrossOrder => 0x63
  | .outrightSeriesFloorTrade => 0x65
  | .allOutrightSeriesElectronicTradesExcludingAwayMarketExecutionsThatWereNotPartOfCertainTransactions => 0x49
  | .allOutrightSeriesTradesGeneratedAsPartOfAnIntermarketSweepOrder => 0x53
  | .transactionIsBeingReportedLateButIsInTheCorrectSequence => 0x44
  | .complexOrderTradesThatWereNotPartOfCertainTransactions => 0x66
  | .complexOrderTradingElectronicallyWithAComplexCubeOrderOrComplexCubeOrderTradingElectronicallyWithComplexCubeContraOrder => 0x67
  | .tradingOfAComplexQccOrderOrCustomerToCustomerCrossOrder => 0x68
  | .complexOrderToComplexOrderFloorTrade => 0x69
  | .complexOrderTradingElectronicallyWithTheOutrightSeriesOrdersquotes => 0x6A
  | .complexOrderToOutrightSeriesOrderFloorTrade => 0x6D
  | .complexOrderWithStockToComplexOrderWithStockFloorTrade => 0x70
  | .complexOrderWithStockToOutrightSeriesOrderFloorTrade => 0x73
  | .extendedHoursTrade => 0x76
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCond1 :=
  if byte = 0x61 then .outrightSeriesOrderquoteTradingElectronicallyWithAOutrightSeriesCubeOrderOrOutrightSeriesCubeOrderTradingElectronicallyWithOutrightSeriesCubeContraOrder
  else if byte = 0x63 then .tradingOfAnOutrightSeriesQccOrderOrCustomerToCustomerCrossOrder
  else if byte = 0x65 then .outrightSeriesFloorTrade
  else if byte = 0x49 then .allOutrightSeriesElectronicTradesExcludingAwayMarketExecutionsThatWereNotPartOfCertainTransactions
  else if byte = 0x53 then .allOutrightSeriesTradesGeneratedAsPartOfAnIntermarketSweepOrder
  else if byte = 0x44 then .transactionIsBeingReportedLateButIsInTheCorrectSequence
  else if byte = 0x66 then .complexOrderTradesThatWereNotPartOfCertainTransactions
  else if byte = 0x67 then .complexOrderTradingElectronicallyWithAComplexCubeOrderOrComplexCubeOrderTradingElectronicallyWithComplexCubeContraOrder
  else if byte = 0x68 then .tradingOfAComplexQccOrderOrCustomerToCustomerCrossOrder
  else if byte = 0x69 then .complexOrderToComplexOrderFloorTrade
  else if byte = 0x6A then .complexOrderTradingElectronicallyWithTheOutrightSeriesOrdersquotes
  else if byte = 0x6D then .complexOrderToOutrightSeriesOrderFloorTrade
  else if byte = 0x70 then .complexOrderWithStockToComplexOrderWithStockFloorTrade
  else if byte = 0x73 then .complexOrderWithStockToOutrightSeriesOrderFloorTrade
  else .extendedHoursTrade

def ofByte (byte : UInt8) : TradeCond1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCond1) : ofByte value.toByte = value := by
  cases value with
  | outrightSeriesOrderquoteTradingElectronicallyWithAOutrightSeriesCubeOrderOrOutrightSeriesCubeOrderTradingElectronicallyWithOutrightSeriesCubeContraOrder => decide
  | tradingOfAnOutrightSeriesQccOrderOrCustomerToCustomerCrossOrder => decide
  | outrightSeriesFloorTrade => decide
  | allOutrightSeriesElectronicTradesExcludingAwayMarketExecutionsThatWereNotPartOfCertainTransactions => decide
  | allOutrightSeriesTradesGeneratedAsPartOfAnIntermarketSweepOrder => decide
  | transactionIsBeingReportedLateButIsInTheCorrectSequence => decide
  | complexOrderTradesThatWereNotPartOfCertainTransactions => decide
  | complexOrderTradingElectronicallyWithAComplexCubeOrderOrComplexCubeOrderTradingElectronicallyWithComplexCubeContraOrder => decide
  | tradingOfAComplexQccOrderOrCustomerToCustomerCrossOrder => decide
  | complexOrderToComplexOrderFloorTrade => decide
  | complexOrderTradingElectronicallyWithTheOutrightSeriesOrdersquotes => decide
  | complexOrderToOutrightSeriesOrderFloorTrade => decide
  | complexOrderWithStockToComplexOrderWithStockFloorTrade => decide
  | complexOrderWithStockToOutrightSeriesOrderFloorTrade => decide
  | extendedHoursTrade => decide
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

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x4F, 0x4D, 0x48]

inductive AuctionType where
  | earlyOpeningAuction -- Early Opening Auction
  | coreOpeningAuction -- Core Opening Auction
  | reopeningAuctionHaltResume -- Reopening Auction Halt Resume
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .earlyOpeningAuction => 0x4F
  | .coreOpeningAuction => 0x4D
  | .reopeningAuctionHaltResume => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x4F then .earlyOpeningAuction
  else if byte = 0x4D then .coreOpeningAuction
  else .reopeningAuctionHaltResume

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | earlyOpeningAuction => decide
  | coreOpeningAuction => decide
  | reopeningAuctionHaltResume => decide
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

/-- Imbalance Side: one byte code -/
def ImbalanceSide.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive ImbalanceSide where
  | buySide -- Buy Side
  | sellSide -- Sell Side
  | spaceOr0X20IndicatesNoImbalance -- Space Or 0 X 20 Indicates No Imbalance
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceSide

def toByte : ImbalanceSide → UInt8
  | .buySide => 0x42
  | .sellSide => 0x53
  | .spaceOr0X20IndicatesNoImbalance => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceSide :=
  if byte = 0x42 then .buySide
  else if byte = 0x53 then .sellSide
  else .spaceOr0X20IndicatesNoImbalance

def ofByte (byte : UInt8) : ImbalanceSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceSide) : ofByte value.toByte = value := by
  cases value with
  | buySide => decide
  | sellSide => decide
  | spaceOr0X20IndicatesNoImbalance => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ImbalanceSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ImbalanceSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ImbalanceSide

/-- Rfq Side: one byte code -/
def RfqSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive RfqSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ RfqSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RfqSide

def toByte : RfqSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RfqSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : RfqSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RfqSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RfqSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RfqSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RfqSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RfqSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RfqSide

/-- Type: one byte code -/
def Type_.codes : List UInt8 :=
  [0x42, 0x43, 0x46, 0x4C, 0x50, 0x53]

inductive Type_ where
  | boldOutrightOnly -- Bold Outright Only
  | coaComplexOnly -- Coa Complex Only
  | flexPriceImprovementCube -- Flex Price Improvement Cube
  | flexAonSolicitationCube -- Flex Aon Solicitation Cube
  | priceImprovementCube -- Price Improvement Cube
  | aonSolicitationCube -- Aon Solicitation Cube
  | unlisted (byte : { byte : UInt8 // byte ∉ Type_.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Type_

def toByte : Type_ → UInt8
  | .boldOutrightOnly => 0x42
  | .coaComplexOnly => 0x43
  | .flexPriceImprovementCube => 0x46
  | .flexAonSolicitationCube => 0x4C
  | .priceImprovementCube => 0x50
  | .aonSolicitationCube => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Type_ :=
  if byte = 0x42 then .boldOutrightOnly
  else if byte = 0x43 then .coaComplexOnly
  else if byte = 0x46 then .flexPriceImprovementCube
  else if byte = 0x4C then .flexAonSolicitationCube
  else if byte = 0x50 then .priceImprovementCube
  else .aonSolicitationCube

def ofByte (byte : UInt8) : Type_ :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Type_) : ofByte value.toByte = value := by
  cases value with
  | boldOutrightOnly => decide
  | coaComplexOnly => decide
  | flexPriceImprovementCube => decide
  | flexAonSolicitationCube => decide
  | priceImprovementCube => decide
  | aonSolicitationCube => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Type_) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Type_ × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Type_) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Type_) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Type_

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x20, 0x30, 0x31, 0x32, 0x33, 0x35, 0x38]

inductive Capacity where
  | naSpaceOr0X20 -- Na Space Or 0 X 20
  | customer -- Customer
  | firm -- Firm
  | brokerDealer -- Broker Dealer
  | marketMaker -- Market Maker
  | awayMarketMaker -- Away Market Maker
  | professionalCustomer -- Professional Customer
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .naSpaceOr0X20 => 0x20
  | .customer => 0x30
  | .firm => 0x31
  | .brokerDealer => 0x32
  | .marketMaker => 0x33
  | .awayMarketMaker => 0x35
  | .professionalCustomer => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x20 then .naSpaceOr0X20
  else if byte = 0x30 then .customer
  else if byte = 0x31 then .firm
  else if byte = 0x32 then .brokerDealer
  else if byte = 0x33 then .marketMaker
  else if byte = 0x35 then .awayMarketMaker
  else .professionalCustomer

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | naSpaceOr0X20 => decide
  | customer => decide
  | firm => decide
  | brokerDealer => decide
  | marketMaker => decide
  | awayMarketMaker => decide
  | professionalCustomer => decide
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

/-- Rfq Status: one byte code -/
def RfqStatus.codes : List UInt8 :=
  [0x4F, 0x51]

inductive RfqStatus where
  | startOfRfqAuction -- Start Of Rfq Auction
  | endOfRfqAuction -- End Of Rfq Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ RfqStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RfqStatus

def toByte : RfqStatus → UInt8
  | .startOfRfqAuction => 0x4F
  | .endOfRfqAuction => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RfqStatus :=
  if byte = 0x4F then .startOfRfqAuction
  else .endOfRfqAuction

def ofByte (byte : UInt8) : RfqStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RfqStatus) : ofByte value.toByte = value := by
  cases value with
  | startOfRfqAuction => decide
  | endOfRfqAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RfqStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RfqStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RfqStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RfqStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RfqStatus

/-- Non Displayed Trade Trade Cond 1: one byte code -/
def NonDisplayedTradeTradeCond1.codes : List UInt8 :=
  [0x61, 0x63, 0x65, 0x49, 0x53, 0x44, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6D, 0x70, 0x73, 0x76, 0x48, 0x46, 0x42]

inductive NonDisplayedTradeTradeCond1 where
  | outrightSeriesOrderquoteTradingElectronicallyWithAOutrightSeriesCubeOrderOrOutrightSeriesCubeOrderTradingElectronicallyWithOutrightSeriesCubeContraOrder -- Outright Series Orderquote Trading Electronically With A Outright Series Cube Order Or Outright Series Cube Order Trading Electronically With Outright Series Cube Contra Order
  | tradingOfAnOutrightSeriesQccOrderOrCustomerToCustomerCrossOrder -- Trading Of An Outright Series Qcc Order Or Customer To Customer Cross Order
  | outrightSeriesFloorTrade -- Outright Series Floor Trade
  | allOutrightSeriesElectronicTradesExcludingAwayMarketExecutionsThatWereNotPartOfCertainTransactions -- All Outright Series Electronic Trades Excluding Away Market Executions That Were Not Part Of Certain Transactions
  | allOutrightSeriesTradesGeneratedAsPartOfAnIntermarketSweepOrder -- All Outright Series Trades Generated As Part Of An Intermarket Sweep Order
  | transactionIsBeingReportedLateButIsInTheCorrectSequence -- Transaction Is Being Reported Late But Is In The Correct Sequence
  | complexOrderTradesThatWereNotPartOfCertainTransactions -- Complex Order Trades That Were Not Part Of Certain Transactions
  | complexOrderTradingElectronicallyWithAComplexCubeOrderOrComplexCubeOrderTradingElectronicallyWithComplexCubeContraOrder -- Complex Order Trading Electronically With A Complex Cube Order Or Complex Cube Order Trading Electronically With Complex Cube Contra Order
  | tradingOfAComplexQccOrderOrCustomerToCustomerCrossOrder -- Trading Of A Complex Qcc Order Or Customer To Customer Cross Order
  | complexOrderToComplexOrderFloorTrade -- Complex Order To Complex Order Floor Trade
  | complexOrderTradingElectronicallyWithTheOutrightSeriesOrdersquotes -- Complex Order Trading Electronically With The Outright Series Ordersquotes
  | complexOrderToOutrightSeriesOrderFloorTrade -- Complex Order To Outright Series Order Floor Trade
  | complexOrderWithStockToComplexOrderWithStockFloorTrade -- Complex Order With Stock To Complex Order With Stock Floor Trade
  | complexOrderWithStockToOutrightSeriesOrderFloorTrade -- Complex Order With Stock To Outright Series Order Floor Trade
  | extendedHoursTrade -- Extended Hours Trade
  | lateReportOfTheOpeningTradeInTheCorrectSequence -- Late Report Of The Opening Trade In The Correct Sequence
  | lateReportOfTheOpeningTradeOutOfSequence -- Late Report Of The Opening Trade Out Of Sequence
  | transactionIsBeingReportedLateAndIsOutOfSequence -- Transaction Is Being Reported Late And Is Out Of Sequence
  | unlisted (byte : { byte : UInt8 // byte ∉ NonDisplayedTradeTradeCond1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NonDisplayedTradeTradeCond1

def toByte : NonDisplayedTradeTradeCond1 → UInt8
  | .outrightSeriesOrderquoteTradingElectronicallyWithAOutrightSeriesCubeOrderOrOutrightSeriesCubeOrderTradingElectronicallyWithOutrightSeriesCubeContraOrder => 0x61
  | .tradingOfAnOutrightSeriesQccOrderOrCustomerToCustomerCrossOrder => 0x63
  | .outrightSeriesFloorTrade => 0x65
  | .allOutrightSeriesElectronicTradesExcludingAwayMarketExecutionsThatWereNotPartOfCertainTransactions => 0x49
  | .allOutrightSeriesTradesGeneratedAsPartOfAnIntermarketSweepOrder => 0x53
  | .transactionIsBeingReportedLateButIsInTheCorrectSequence => 0x44
  | .complexOrderTradesThatWereNotPartOfCertainTransactions => 0x66
  | .complexOrderTradingElectronicallyWithAComplexCubeOrderOrComplexCubeOrderTradingElectronicallyWithComplexCubeContraOrder => 0x67
  | .tradingOfAComplexQccOrderOrCustomerToCustomerCrossOrder => 0x68
  | .complexOrderToComplexOrderFloorTrade => 0x69
  | .complexOrderTradingElectronicallyWithTheOutrightSeriesOrdersquotes => 0x6A
  | .complexOrderToOutrightSeriesOrderFloorTrade => 0x6D
  | .complexOrderWithStockToComplexOrderWithStockFloorTrade => 0x70
  | .complexOrderWithStockToOutrightSeriesOrderFloorTrade => 0x73
  | .extendedHoursTrade => 0x76
  | .lateReportOfTheOpeningTradeInTheCorrectSequence => 0x48
  | .lateReportOfTheOpeningTradeOutOfSequence => 0x46
  | .transactionIsBeingReportedLateAndIsOutOfSequence => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NonDisplayedTradeTradeCond1 :=
  if byte = 0x61 then .outrightSeriesOrderquoteTradingElectronicallyWithAOutrightSeriesCubeOrderOrOutrightSeriesCubeOrderTradingElectronicallyWithOutrightSeriesCubeContraOrder
  else if byte = 0x63 then .tradingOfAnOutrightSeriesQccOrderOrCustomerToCustomerCrossOrder
  else if byte = 0x65 then .outrightSeriesFloorTrade
  else if byte = 0x49 then .allOutrightSeriesElectronicTradesExcludingAwayMarketExecutionsThatWereNotPartOfCertainTransactions
  else if byte = 0x53 then .allOutrightSeriesTradesGeneratedAsPartOfAnIntermarketSweepOrder
  else if byte = 0x44 then .transactionIsBeingReportedLateButIsInTheCorrectSequence
  else if byte = 0x66 then .complexOrderTradesThatWereNotPartOfCertainTransactions
  else if byte = 0x67 then .complexOrderTradingElectronicallyWithAComplexCubeOrderOrComplexCubeOrderTradingElectronicallyWithComplexCubeContraOrder
  else if byte = 0x68 then .tradingOfAComplexQccOrderOrCustomerToCustomerCrossOrder
  else if byte = 0x69 then .complexOrderToComplexOrderFloorTrade
  else if byte = 0x6A then .complexOrderTradingElectronicallyWithTheOutrightSeriesOrdersquotes
  else if byte = 0x6D then .complexOrderToOutrightSeriesOrderFloorTrade
  else if byte = 0x70 then .complexOrderWithStockToComplexOrderWithStockFloorTrade
  else if byte = 0x73 then .complexOrderWithStockToOutrightSeriesOrderFloorTrade
  else if byte = 0x76 then .extendedHoursTrade
  else if byte = 0x48 then .lateReportOfTheOpeningTradeInTheCorrectSequence
  else if byte = 0x46 then .lateReportOfTheOpeningTradeOutOfSequence
  else .transactionIsBeingReportedLateAndIsOutOfSequence

def ofByte (byte : UInt8) : NonDisplayedTradeTradeCond1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NonDisplayedTradeTradeCond1) : ofByte value.toByte = value := by
  cases value with
  | outrightSeriesOrderquoteTradingElectronicallyWithAOutrightSeriesCubeOrderOrOutrightSeriesCubeOrderTradingElectronicallyWithOutrightSeriesCubeContraOrder => decide
  | tradingOfAnOutrightSeriesQccOrderOrCustomerToCustomerCrossOrder => decide
  | outrightSeriesFloorTrade => decide
  | allOutrightSeriesElectronicTradesExcludingAwayMarketExecutionsThatWereNotPartOfCertainTransactions => decide
  | allOutrightSeriesTradesGeneratedAsPartOfAnIntermarketSweepOrder => decide
  | transactionIsBeingReportedLateButIsInTheCorrectSequence => decide
  | complexOrderTradesThatWereNotPartOfCertainTransactions => decide
  | complexOrderTradingElectronicallyWithAComplexCubeOrderOrComplexCubeOrderTradingElectronicallyWithComplexCubeContraOrder => decide
  | tradingOfAComplexQccOrderOrCustomerToCustomerCrossOrder => decide
  | complexOrderToComplexOrderFloorTrade => decide
  | complexOrderTradingElectronicallyWithTheOutrightSeriesOrdersquotes => decide
  | complexOrderToOutrightSeriesOrderFloorTrade => decide
  | complexOrderWithStockToComplexOrderWithStockFloorTrade => decide
  | complexOrderWithStockToOutrightSeriesOrderFloorTrade => decide
  | extendedHoursTrade => decide
  | lateReportOfTheOpeningTradeInTheCorrectSequence => decide
  | lateReportOfTheOpeningTradeOutOfSequence => decide
  | transactionIsBeingReportedLateAndIsOutOfSequence => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NonDisplayedTradeTradeCond1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NonDisplayedTradeTradeCond1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NonDisplayedTradeTradeCond1) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NonDisplayedTradeTradeCond1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NonDisplayedTradeTradeCond1

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x45, 0x4F, 0x35]

inductive CrossType where
  | marketCenterEarlyOpeningAuction -- Market Center Early Opening Auction
  | marketCenterOpeningAuction -- Market Center Opening Auction
  | marketCenterReopeningAuction -- Market Center Reopening Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .marketCenterEarlyOpeningAuction => 0x45
  | .marketCenterOpeningAuction => 0x4F
  | .marketCenterReopeningAuction => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x45 then .marketCenterEarlyOpeningAuction
  else if byte = 0x4F then .marketCenterOpeningAuction
  else .marketCenterReopeningAuction

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | marketCenterEarlyOpeningAuction => decide
  | marketCenterOpeningAuction => decide
  | marketCenterReopeningAuction => decide
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
  reserved2 : Alpha 2
  secondReserved2 : Alpha 2
  thirdReserved2 : Alpha 2
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
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.secondReserved2
    ++ (Alpha.encode message.thirdReserved2)))))))))))))))

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
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (thirdReserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ symbolIndex, symbol, reserved1, marketId, systemId, exchangeCode, priceScaleCode, securityType, lotSize, prevClosePrice, prevCloseVolume, priceResolution, roundLot, reserved2, secondReserved2, thirdReserved2 }, bytes)

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolIndexMappingMessage

/-- Symbol Clear Message: 16 bytes -/
structure SymbolClearMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  nextSourceSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace SymbolClearMessage

def encode (message : SymbolClearMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.nextSourceSeqNum)))

def decode (bytes : List UInt8) : Option (SymbolClearMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (nextSourceSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, nextSourceSeqNum }, bytes)

@[simp] theorem encode_length (message : SymbolClearMessage) : (encode message).length = 16 := by
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
  reserved4 : Alpha 4
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
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 4 message.price1
    ++ (encodeUIntLE 4 message.price2
    ++ (SsrTriggeringExchangeId.encode message.ssrTriggeringExchangeId
    ++ (encodeUIntLE 4 message.ssrTriggeringVolume
    ++ (encodeUIntLE 4 message.time
    ++ (SsrState.encode message.ssrState
    ++ (MarketState.encode message.marketState
    ++ (Alpha.encode message.sessionState))))))))))))))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (haltCondition, bytes) ← HaltCondition.decode bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (price1, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 4 bytes
  let (ssrTriggeringExchangeId, bytes) ← SsrTriggeringExchangeId.decode bytes
  let (ssrTriggeringVolume, bytes) ← decodeUIntLE 4 bytes
  let (time, bytes) ← decodeUIntLE 4 bytes
  let (ssrState, bytes) ← SsrState.decode bytes
  let (marketState, bytes) ← MarketState.decode bytes
  let (sessionState, bytes) ← Alpha.decode 1 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, securityStatus, haltCondition, reserved4, price1, price2, ssrTriggeringExchangeId, ssrTriggeringVolume, time, ssrState, marketState, sessionState }, bytes)

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

/-- Outright Series Index Mapping Message: 51 bytes -/
structure OutrightSeriesIndexMappingMessage where
  seriesIndex : BitVec 32
  seriesType : BitVec 8
  marketId : BitVec 16
  systemId : BitVec 8
  optionSymbolRoot : Alpha 6
  underlyingSymbol : Alpha 11
  underlyingIndex : BitVec 32
  priceScaleCode : BitVec 8
  contractMultiplier : BitVec 16
  maturityDate : Alpha 6
  putOrCall : BitVec 8
  strikePrice : Alpha 10
  closingOnlyIndicator : ClosingOnlyIndicator
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace OutrightSeriesIndexMappingMessage

def encode (message : OutrightSeriesIndexMappingMessage) : List UInt8 :=
  encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 1 message.seriesType
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUIntLE 1 message.systemId
    ++ (Alpha.encode message.optionSymbolRoot
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.underlyingIndex
    ++ (encodeUIntLE 1 message.priceScaleCode
    ++ (encodeUIntLE 2 message.contractMultiplier
    ++ (Alpha.encode message.maturityDate
    ++ (encodeUIntLE 1 message.putOrCall
    ++ (Alpha.encode message.strikePrice
    ++ (ClosingOnlyIndicator.encode message.closingOnlyIndicator
    ++ (Alpha.encode message.reserved1)))))))))))))

def decode (bytes : List UInt8) : Option (OutrightSeriesIndexMappingMessage × List UInt8) := do
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesType, bytes) ← decodeUIntLE 1 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (systemId, bytes) ← decodeUIntLE 1 bytes
  let (optionSymbolRoot, bytes) ← Alpha.decode 6 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (underlyingIndex, bytes) ← decodeUIntLE 4 bytes
  let (priceScaleCode, bytes) ← decodeUIntLE 1 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (maturityDate, bytes) ← Alpha.decode 6 bytes
  let (putOrCall, bytes) ← decodeUIntLE 1 bytes
  let (strikePrice, bytes) ← Alpha.decode 10 bytes
  let (closingOnlyIndicator, bytes) ← ClosingOnlyIndicator.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ seriesIndex, seriesType, marketId, systemId, optionSymbolRoot, underlyingSymbol, underlyingIndex, priceScaleCode, contractMultiplier, maturityDate, putOrCall, strikePrice, closingOnlyIndicator, reserved1 }, bytes)

@[simp] theorem encode_length (message : OutrightSeriesIndexMappingMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ClosingOnlyIndicator.encode_length]

theorem encode_length_pos (message : OutrightSeriesIndexMappingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightSeriesIndexMappingMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClosingOnlyIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutrightSeriesIndexMappingMessage

/-- Options Status Message: 19 bytes -/
structure OptionsStatusMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  seriesStatus : SeriesStatus
  marketState : MarketState
  optionsStatusHaltCondition : OptionsStatusHaltCondition
  deriving DecidableEq, Repr

namespace OptionsStatusMessage

def encode (message : OptionsStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (MarketState.encode message.marketState
    ++ (OptionsStatusHaltCondition.encode message.optionsStatusHaltCondition))))))

def decode (bytes : List UInt8) : Option (OptionsStatusMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (marketState, bytes) ← MarketState.decode bytes
  let (optionsStatusHaltCondition, bytes) ← OptionsStatusHaltCondition.decode bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, seriesSeqNum, seriesStatus, marketState, optionsStatusHaltCondition }, bytes)

@[simp] theorem encode_length (message : OptionsStatusMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SeriesStatus.encode_length, MarketState.encode_length, OptionsStatusHaltCondition.encode_length]

theorem encode_length_pos (message : OptionsStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsStatusMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketState.decode_encode, some_bind]
  dsimp only
  rw [OptionsStatusHaltCondition.decode_encode, some_bind]
  rfl

end OptionsStatusMessage

/-- Complex Series Index Mapping Leg: 8 bytes -/
structure ComplexSeriesIndexMappingLeg where
  symbolIndex : BitVec 32
  legRatioQty : BitVec 16
  legSide : LegSide
  legSecurityType : LegSecurityType
  deriving DecidableEq, Repr

namespace ComplexSeriesIndexMappingLeg

def encode (message : ComplexSeriesIndexMappingLeg) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 2 message.legRatioQty
    ++ (LegSide.encode message.legSide
    ++ (LegSecurityType.encode message.legSecurityType)))

def decode (bytes : List UInt8) : Option (ComplexSeriesIndexMappingLeg × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 2 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (legSecurityType, bytes) ← LegSecurityType.decode bytes
  pure ({ symbolIndex, legRatioQty, legSide, legSecurityType }, bytes)

@[simp] theorem encode_length (message : ComplexSeriesIndexMappingLeg) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, LegSide.encode_length, LegSecurityType.encode_length]

theorem encode_length_pos (message : ComplexSeriesIndexMappingLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexSeriesIndexMappingLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
  dsimp only
  rw [LegSecurityType.decode_encode, some_bind]
  rfl

end ComplexSeriesIndexMappingLeg

/-- Complex Series Index Mapping Message -/
structure ComplexSeriesIndexMappingMessage where
  seriesIndex : BitVec 32
  marketId : BitVec 16
  systemId : BitVec 8
  complexSeriesIndexMappingLeg : Bounded 2 ComplexSeriesIndexMappingLeg
  deriving DecidableEq, Repr

namespace ComplexSeriesIndexMappingMessage

def encode (message : ComplexSeriesIndexMappingMessage) : List UInt8 :=
  encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUIntLE 1 message.systemId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.complexSeriesIndexMappingLeg.val.length)
    ++ (encodeMany ComplexSeriesIndexMappingLeg.encode message.complexSeriesIndexMappingLeg.val))))

def decode (bytes : List UInt8) : Option (ComplexSeriesIndexMappingMessage × List UInt8) := do
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (systemId, bytes) ← decodeUIntLE 1 bytes
  let (noOfLegs, bytes) ← decodeUIntLE 2 bytes
  let (complexSeriesIndexMappingLeg_, bytes) ← decodeMany ComplexSeriesIndexMappingLeg.decode noOfLegs.toNat bytes
  if fits_complexSeriesIndexMappingLeg : complexSeriesIndexMappingLeg_.length < 256 ^ 2 then
    pure ({ seriesIndex, marketId, systemId, complexSeriesIndexMappingLeg := ⟨complexSeriesIndexMappingLeg_, fits_complexSeriesIndexMappingLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexSeriesIndexMappingMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexSeriesIndexMappingMessage) : (encode message).length ≤ 524289 := by
  have bound_complexSeriesIndexMappingLeg := message.complexSeriesIndexMappingLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const ComplexSeriesIndexMappingLeg.encode 8 ComplexSeriesIndexMappingLeg.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexSeriesIndexMappingMessage) (rest : List UInt8) :
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
  rw [decodeMany_bounded 2 ComplexSeriesIndexMappingLeg.encode ComplexSeriesIndexMappingLeg.decode ComplexSeriesIndexMappingLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.complexSeriesIndexMappingLeg.length_lt]
  rfl

end ComplexSeriesIndexMappingMessage

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
  | shortRefreshHeader (tag : { v : BitVec 16 // v ≠ 1 }) -- any other value, read as nothing
  deriving DecidableEq, Repr

namespace RefreshHeaderLayout

/-- The Current Refresh Pkt each message is sent under -/
def tag : RefreshHeaderLayout → BitVec 16
  | .fullRefreshHeader _ => 1
  | .shortRefreshHeader tag => tag.val

def encode : RefreshHeaderLayout → List UInt8
  | .fullRefreshHeader message => FullRefreshHeader.encode message
  | .shortRefreshHeader _ => []

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : RefreshHeaderLayout) : (encode message).length ≤ 8 := by
  cases message with
  | fullRefreshHeader inner =>
    simp only [encode, FullRefreshHeader.encode_length]
    omega
  | shortRefreshHeader _ =>
    simp only [encode, List.length_nil]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (RefreshHeaderLayout × List UInt8) :=
  if h0 : tag = 1 then (FullRefreshHeader.decode bytes).map fun (message, rest) => (.fullRefreshHeader message, rest)
  else some (.shortRefreshHeader ⟨tag, h0⟩, bytes)

@[simp] theorem decode_encode (message : RefreshHeaderLayout) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message with
  | fullRefreshHeader m => simp [decode, encode, tag]
  | shortRefreshHeader t =>
    obtain ⟨v, h0⟩ := t
    simp only [tag, encode, decode, h0, List.nil_append, reduceDIte]

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
  | shortRefreshHeader _ =>
    simp only [RefreshHeaderLayout.encode, List.length_nil, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
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

/-- Options Add Order Message: 36 bytes -/
structure OptionsAddOrderMessage where
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  orderId : BitVec 64
  price : BitVec 32
  volume : BitVec 32
  side : Side
  firmId : Alpha 5
  reserved1 : Alpha 1
  custIndicator : CustIndicator
  deriving DecidableEq, Repr

namespace OptionsAddOrderMessage

def encode (message : OptionsAddOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (Side.encode message.side
    ++ (Alpha.encode message.firmId
    ++ (Alpha.encode message.reserved1
    ++ (CustIndicator.encode message.custIndicator)))))))))

def decode (bytes : List UInt8) : Option (OptionsAddOrderMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (firmId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (custIndicator, bytes) ← CustIndicator.decode bytes
  pure ({ sourceTimeNs, seriesIndex, seriesSeqNum, orderId, price, volume, side, firmId, reserved1, custIndicator }, bytes)

@[simp] theorem encode_length (message : OptionsAddOrderMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length, CustIndicator.encode_length]

theorem encode_length_pos (message : OptionsAddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsAddOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [CustIndicator.decode_encode, some_bind]
  rfl

end OptionsAddOrderMessage

/-- Options Modify Order Message: 31 bytes -/
structure OptionsModifyOrderMessage where
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  orderId : BitVec 64
  price : BitVec 32
  volume : BitVec 32
  positionChange : BitVec 8
  side : Side
  custIndicator : CustIndicator
  deriving DecidableEq, Repr

namespace OptionsModifyOrderMessage

def encode (message : OptionsModifyOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 1 message.positionChange
    ++ (Side.encode message.side
    ++ (CustIndicator.encode message.custIndicator))))))))

def decode (bytes : List UInt8) : Option (OptionsModifyOrderMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (positionChange, bytes) ← decodeUIntLE 1 bytes
  let (side, bytes) ← Side.decode bytes
  let (custIndicator, bytes) ← CustIndicator.decode bytes
  pure ({ sourceTimeNs, seriesIndex, seriesSeqNum, orderId, price, volume, positionChange, side, custIndicator }, bytes)

@[simp] theorem encode_length (message : OptionsModifyOrderMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, CustIndicator.encode_length]

theorem encode_length_pos (message : OptionsModifyOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsModifyOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [CustIndicator.decode_encode, some_bind]
  rfl

end OptionsModifyOrderMessage

/-- Options Delete Order Message: 21 bytes -/
structure OptionsDeleteOrderMessage where
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  orderId : BitVec 64
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace OptionsDeleteOrderMessage

def encode (message : OptionsDeleteOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (encodeUIntLE 8 message.orderId
    ++ (Alpha.encode message.reserved1))))

def decode (bytes : List UInt8) : Option (OptionsDeleteOrderMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ sourceTimeNs, seriesIndex, seriesSeqNum, orderId, reserved1 }, bytes)

@[simp] theorem encode_length (message : OptionsDeleteOrderMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OptionsDeleteOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsDeleteOrderMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionsDeleteOrderMessage

/-- Options Order Execution Message: 38 bytes -/
structure OptionsOrderExecutionMessage where
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  orderId : BitVec 64
  tradeId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  printableFlag : BitVec 8
  reserved1 : Alpha 1
  tradeCond1 : TradeCond1
  reserved3 : Alpha 3
  deriving DecidableEq, Repr

namespace OptionsOrderExecutionMessage

def encode (message : OptionsOrderExecutionMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 1 message.printableFlag
    ++ (Alpha.encode message.reserved1
    ++ (TradeCond1.encode message.tradeCond1
    ++ (Alpha.encode message.reserved3))))))))))

def decode (bytes : List UInt8) : Option (OptionsOrderExecutionMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (printableFlag, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (tradeCond1, bytes) ← TradeCond1.decode bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  pure ({ sourceTimeNs, seriesIndex, seriesSeqNum, orderId, tradeId, price, volume, printableFlag, reserved1, tradeCond1, reserved3 }, bytes)

@[simp] theorem encode_length (message : OptionsOrderExecutionMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradeCond1.encode_length]

theorem encode_length_pos (message : OptionsOrderExecutionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsOrderExecutionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCond1.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionsOrderExecutionMessage

/-- Options Replace Order Message: 39 bytes -/
structure OptionsReplaceOrderMessage where
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  orderId : BitVec 64
  newOrderId : BitVec 64
  price : BitVec 32
  volume : BitVec 32
  side : Side
  reserved1 : Alpha 1
  custIndicator : CustIndicator
  deriving DecidableEq, Repr

namespace OptionsReplaceOrderMessage

def encode (message : OptionsReplaceOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.newOrderId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (Side.encode message.side
    ++ (Alpha.encode message.reserved1
    ++ (CustIndicator.encode message.custIndicator)))))))))

def decode (bytes : List UInt8) : Option (OptionsReplaceOrderMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (newOrderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (custIndicator, bytes) ← CustIndicator.decode bytes
  pure ({ sourceTimeNs, seriesIndex, seriesSeqNum, orderId, newOrderId, price, volume, side, reserved1, custIndicator }, bytes)

@[simp] theorem encode_length (message : OptionsReplaceOrderMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length, CustIndicator.encode_length]

theorem encode_length_pos (message : OptionsReplaceOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsReplaceOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [CustIndicator.decode_encode, some_bind]
  rfl

end OptionsReplaceOrderMessage

/-- Options Imbalance Message: 61 bytes -/
structure OptionsImbalanceMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  reserved4 : Alpha 4
  pairedQty : BitVec 32
  totalImbalanceQty : BitVec 32
  marketImbalanceQty : BitVec 32
  reserved2 : Alpha 2
  auctionType : AuctionType
  imbalanceSide : ImbalanceSide
  continuousBookClearingPrice : BitVec 32
  auctionInterestClearingPrice : BitVec 32
  secondReserved4 : Alpha 4
  indicativeMatchPrice : BitVec 32
  upperCollar : BitVec 32
  lowerCollar : BitVec 32
  auctionStatus : BitVec 8
  deriving DecidableEq, Repr

namespace OptionsImbalanceMessage

def encode (message : OptionsImbalanceMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 4 message.pairedQty
    ++ (encodeUIntLE 4 message.totalImbalanceQty
    ++ (encodeUIntLE 4 message.marketImbalanceQty
    ++ (Alpha.encode message.reserved2
    ++ (AuctionType.encode message.auctionType
    ++ (ImbalanceSide.encode message.imbalanceSide
    ++ (encodeUIntLE 4 message.continuousBookClearingPrice
    ++ (encodeUIntLE 4 message.auctionInterestClearingPrice
    ++ (Alpha.encode message.secondReserved4
    ++ (encodeUIntLE 4 message.indicativeMatchPrice
    ++ (encodeUIntLE 4 message.upperCollar
    ++ (encodeUIntLE 4 message.lowerCollar
    ++ (encodeUIntLE 1 message.auctionStatus)))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionsImbalanceMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (pairedQty, bytes) ← decodeUIntLE 4 bytes
  let (totalImbalanceQty, bytes) ← decodeUIntLE 4 bytes
  let (marketImbalanceQty, bytes) ← decodeUIntLE 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (imbalanceSide, bytes) ← ImbalanceSide.decode bytes
  let (continuousBookClearingPrice, bytes) ← decodeUIntLE 4 bytes
  let (auctionInterestClearingPrice, bytes) ← decodeUIntLE 4 bytes
  let (secondReserved4, bytes) ← Alpha.decode 4 bytes
  let (indicativeMatchPrice, bytes) ← decodeUIntLE 4 bytes
  let (upperCollar, bytes) ← decodeUIntLE 4 bytes
  let (lowerCollar, bytes) ← decodeUIntLE 4 bytes
  let (auctionStatus, bytes) ← decodeUIntLE 1 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, seriesSeqNum, reserved4, pairedQty, totalImbalanceQty, marketImbalanceQty, reserved2, auctionType, imbalanceSide, continuousBookClearingPrice, auctionInterestClearingPrice, secondReserved4, indicativeMatchPrice, upperCollar, lowerCollar, auctionStatus }, bytes)

@[simp] theorem encode_length (message : OptionsImbalanceMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, AuctionType.encode_length, ImbalanceSide.encode_length]

theorem encode_length_pos (message : OptionsImbalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsImbalanceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ImbalanceSide.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OptionsImbalanceMessage

/-- Options Add Order Refresh Message: 40 bytes -/
structure OptionsAddOrderRefreshMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  orderId : BitVec 64
  price : BitVec 32
  volume : BitVec 32
  side : Side
  firmId : Alpha 5
  reserved1 : Alpha 1
  custIndicator : CustIndicator
  deriving DecidableEq, Repr

namespace OptionsAddOrderRefreshMessage

def encode (message : OptionsAddOrderRefreshMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (Side.encode message.side
    ++ (Alpha.encode message.firmId
    ++ (Alpha.encode message.reserved1
    ++ (CustIndicator.encode message.custIndicator))))))))))

def decode (bytes : List UInt8) : Option (OptionsAddOrderRefreshMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (firmId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (custIndicator, bytes) ← CustIndicator.decode bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, seriesSeqNum, orderId, price, volume, side, firmId, reserved1, custIndicator }, bytes)

@[simp] theorem encode_length (message : OptionsAddOrderRefreshMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length, CustIndicator.encode_length]

theorem encode_length_pos (message : OptionsAddOrderRefreshMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsAddOrderRefreshMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [CustIndicator.decode_encode, some_bind]
  rfl

end OptionsAddOrderRefreshMessage

/-- Options Series Rfq Message: 40 bytes -/
structure OptionsSeriesRfqMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  rfqSide : RfqSide
  type : Type_
  capacity : Capacity
  totalQuantity : BitVec 32
  workingPrice : BitVec 32
  participant : BitVec 32
  auctionId : BitVec 64
  rfqStatus : RfqStatus
  deriving DecidableEq, Repr

namespace OptionsSeriesRfqMessage

def encode (message : OptionsSeriesRfqMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (RfqSide.encode message.rfqSide
    ++ (Type_.encode message.type
    ++ (Capacity.encode message.capacity
    ++ (encodeUIntLE 4 message.totalQuantity
    ++ (encodeUIntLE 4 message.workingPrice
    ++ (encodeUIntLE 4 message.participant
    ++ (encodeUIntLE 8 message.auctionId
    ++ (RfqStatus.encode message.rfqStatus)))))))))))

def decode (bytes : List UInt8) : Option (OptionsSeriesRfqMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (rfqSide, bytes) ← RfqSide.decode bytes
  let (type, bytes) ← Type_.decode bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (totalQuantity, bytes) ← decodeUIntLE 4 bytes
  let (workingPrice, bytes) ← decodeUIntLE 4 bytes
  let (participant, bytes) ← decodeUIntLE 4 bytes
  let (auctionId, bytes) ← decodeUIntLE 8 bytes
  let (rfqStatus, bytes) ← RfqStatus.decode bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, seriesSeqNum, rfqSide, type, capacity, totalQuantity, workingPrice, participant, auctionId, rfqStatus }, bytes)

@[simp] theorem encode_length (message : OptionsSeriesRfqMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, RfqSide.encode_length, Type_.encode_length, Capacity.encode_length, RfqStatus.encode_length]

theorem encode_length_pos (message : OptionsSeriesRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsSeriesRfqMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, RfqSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Type_.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [RfqStatus.decode_encode, some_bind]
  rfl

end OptionsSeriesRfqMessage

/-- Options Non Displayed Trade Message: 30 bytes -/
structure OptionsNonDisplayedTradeMessage where
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  printableFlag : BitVec 8
  nonDisplayedTradeTradeCond1 : NonDisplayedTradeTradeCond1
  reserved3 : Alpha 3
  priceType : BitVec 8
  deriving DecidableEq, Repr

namespace OptionsNonDisplayedTradeMessage

def encode (message : OptionsNonDisplayedTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 1 message.printableFlag
    ++ (NonDisplayedTradeTradeCond1.encode message.nonDisplayedTradeTradeCond1
    ++ (Alpha.encode message.reserved3
    ++ (encodeUIntLE 1 message.priceType)))))))))

def decode (bytes : List UInt8) : Option (OptionsNonDisplayedTradeMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (printableFlag, bytes) ← decodeUIntLE 1 bytes
  let (nonDisplayedTradeTradeCond1, bytes) ← NonDisplayedTradeTradeCond1.decode bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  let (priceType, bytes) ← decodeUIntLE 1 bytes
  pure ({ sourceTimeNs, seriesIndex, seriesSeqNum, tradeId, price, volume, printableFlag, nonDisplayedTradeTradeCond1, reserved3, priceType }, bytes)

@[simp] theorem encode_length (message : OptionsNonDisplayedTradeMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, NonDisplayedTradeTradeCond1.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OptionsNonDisplayedTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsNonDisplayedTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, NonDisplayedTradeTradeCond1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OptionsNonDisplayedTradeMessage

/-- Options Cross Trade Message: 25 bytes -/
structure OptionsCrossTradeMessage where
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  crossId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  crossType : CrossType
  deriving DecidableEq, Repr

namespace OptionsCrossTradeMessage

def encode (message : OptionsCrossTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (encodeUIntLE 4 message.crossId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (CrossType.encode message.crossType))))))

def decode (bytes : List UInt8) : Option (OptionsCrossTradeMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (crossId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  pure ({ sourceTimeNs, seriesIndex, seriesSeqNum, crossId, price, volume, crossType }, bytes)

@[simp] theorem encode_length (message : OptionsCrossTradeMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, CrossType.encode_length]

theorem encode_length_pos (message : OptionsCrossTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsCrossTradeMessage) (rest : List UInt8) :
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
  rw [CrossType.decode_encode, some_bind]
  rfl

end OptionsCrossTradeMessage

/-- Options Trade Cancel Message: 16 bytes -/
structure OptionsTradeCancelMessage where
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  tradeId : BitVec 32
  deriving DecidableEq, Repr

namespace OptionsTradeCancelMessage

def encode (message : OptionsTradeCancelMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (encodeUIntLE 4 message.tradeId)))

def decode (bytes : List UInt8) : Option (OptionsTradeCancelMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTimeNs, seriesIndex, seriesSeqNum, tradeId }, bytes)

@[simp] theorem encode_length (message : OptionsTradeCancelMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OptionsTradeCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsTradeCancelMessage) (rest : List UInt8) :
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

end OptionsTradeCancelMessage

/-- Options Outright Series Summary Message: 32 bytes -/
structure OptionsOutrightSeriesSummaryMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  highPrice : BitVec 32
  lowPrice : BitVec 32
  open_ : BitVec 32
  close : BitVec 32
  totalVolume : BitVec 32
  deriving DecidableEq, Repr

namespace OptionsOutrightSeriesSummaryMessage

def encode (message : OptionsOutrightSeriesSummaryMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.highPrice
    ++ (encodeUIntLE 4 message.lowPrice
    ++ (encodeUIntLE 4 message.open_
    ++ (encodeUIntLE 4 message.close
    ++ (encodeUIntLE 4 message.totalVolume)))))))

def decode (bytes : List UInt8) : Option (OptionsOutrightSeriesSummaryMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (highPrice, bytes) ← decodeUIntLE 4 bytes
  let (lowPrice, bytes) ← decodeUIntLE 4 bytes
  let (open_, bytes) ← decodeUIntLE 4 bytes
  let (close, bytes) ← decodeUIntLE 4 bytes
  let (totalVolume, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, highPrice, lowPrice, open_, close, totalVolume }, bytes)

@[simp] theorem encode_length (message : OptionsOutrightSeriesSummaryMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OptionsOutrightSeriesSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsOutrightSeriesSummaryMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OptionsOutrightSeriesSummaryMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | sequenceNumberResetMessage (message : SequenceNumberResetMessage) -- 1
  | sourceTimeReferenceMessage (message : SourceTimeReferenceMessage) -- 2
  | symbolIndexMappingMessage (message : SymbolIndexMappingMessage) -- 3
  | symbolClearMessage (message : SymbolClearMessage) -- 32
  | securityStatusMessage (message : SecurityStatusMessage) -- 34
  | outrightSeriesIndexMappingMessage (message : OutrightSeriesIndexMappingMessage) -- 50
  | optionsStatusMessage (message : OptionsStatusMessage) -- 51
  | complexSeriesIndexMappingMessage (message : ComplexSeriesIndexMappingMessage) -- 60
  | retransmissionRequestMessage (message : RetransmissionRequestMessage) -- 10
  | refreshHeaderMessage (message : RefreshHeaderMessage) -- 35
  | refreshRequestMessage (message : RefreshRequestMessage) -- 15
  | symbolIndexMappingRequestMessage (message : SymbolIndexMappingRequestMessage) -- 13
  | messageUnavailableMessage (message : MessageUnavailableMessage) -- 31
  | requestResponseMessage (message : RequestResponseMessage) -- 11
  | heartbeatResponseMessage (message : HeartbeatResponseMessage) -- 12
  | optionsAddOrderMessage (message : OptionsAddOrderMessage) -- 300
  | optionsModifyOrderMessage (message : OptionsModifyOrderMessage) -- 301
  | optionsDeleteOrderMessage (message : OptionsDeleteOrderMessage) -- 302
  | optionsOrderExecutionMessage (message : OptionsOrderExecutionMessage) -- 303
  | optionsReplaceOrderMessage (message : OptionsReplaceOrderMessage) -- 304
  | optionsImbalanceMessage (message : OptionsImbalanceMessage) -- 305
  | optionsAddOrderRefreshMessage (message : OptionsAddOrderRefreshMessage) -- 306
  | optionsSeriesRfqMessage (message : OptionsSeriesRfqMessage) -- 307
  | optionsNonDisplayedTradeMessage (message : OptionsNonDisplayedTradeMessage) -- 310
  | optionsCrossTradeMessage (message : OptionsCrossTradeMessage) -- 311
  | optionsTradeCancelMessage (message : OptionsTradeCancelMessage) -- 312
  | optionsOutrightSeriesSummaryMessage (message : OptionsOutrightSeriesSummaryMessage) -- 323
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceNumberResetMessage _ => 1
  | .sourceTimeReferenceMessage _ => 2
  | .symbolIndexMappingMessage _ => 3
  | .symbolClearMessage _ => 32
  | .securityStatusMessage _ => 34
  | .outrightSeriesIndexMappingMessage _ => 50
  | .optionsStatusMessage _ => 51
  | .complexSeriesIndexMappingMessage _ => 60
  | .retransmissionRequestMessage _ => 10
  | .refreshHeaderMessage _ => 35
  | .refreshRequestMessage _ => 15
  | .symbolIndexMappingRequestMessage _ => 13
  | .messageUnavailableMessage _ => 31
  | .requestResponseMessage _ => 11
  | .heartbeatResponseMessage _ => 12
  | .optionsAddOrderMessage _ => 300
  | .optionsModifyOrderMessage _ => 301
  | .optionsDeleteOrderMessage _ => 302
  | .optionsOrderExecutionMessage _ => 303
  | .optionsReplaceOrderMessage _ => 304
  | .optionsImbalanceMessage _ => 305
  | .optionsAddOrderRefreshMessage _ => 306
  | .optionsSeriesRfqMessage _ => 307
  | .optionsNonDisplayedTradeMessage _ => 310
  | .optionsCrossTradeMessage _ => 311
  | .optionsTradeCancelMessage _ => 312
  | .optionsOutrightSeriesSummaryMessage _ => 323

def encode : Payload → List UInt8
  | .sequenceNumberResetMessage message => SequenceNumberResetMessage.encode message
  | .sourceTimeReferenceMessage message => SourceTimeReferenceMessage.encode message
  | .symbolIndexMappingMessage message => SymbolIndexMappingMessage.encode message
  | .symbolClearMessage message => SymbolClearMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .outrightSeriesIndexMappingMessage message => OutrightSeriesIndexMappingMessage.encode message
  | .optionsStatusMessage message => OptionsStatusMessage.encode message
  | .complexSeriesIndexMappingMessage message => ComplexSeriesIndexMappingMessage.encode message
  | .retransmissionRequestMessage message => RetransmissionRequestMessage.encode message
  | .refreshHeaderMessage message => RefreshHeaderMessage.encode message
  | .refreshRequestMessage message => RefreshRequestMessage.encode message
  | .symbolIndexMappingRequestMessage message => SymbolIndexMappingRequestMessage.encode message
  | .messageUnavailableMessage message => MessageUnavailableMessage.encode message
  | .requestResponseMessage message => RequestResponseMessage.encode message
  | .heartbeatResponseMessage message => HeartbeatResponseMessage.encode message
  | .optionsAddOrderMessage message => OptionsAddOrderMessage.encode message
  | .optionsModifyOrderMessage message => OptionsModifyOrderMessage.encode message
  | .optionsDeleteOrderMessage message => OptionsDeleteOrderMessage.encode message
  | .optionsOrderExecutionMessage message => OptionsOrderExecutionMessage.encode message
  | .optionsReplaceOrderMessage message => OptionsReplaceOrderMessage.encode message
  | .optionsImbalanceMessage message => OptionsImbalanceMessage.encode message
  | .optionsAddOrderRefreshMessage message => OptionsAddOrderRefreshMessage.encode message
  | .optionsSeriesRfqMessage message => OptionsSeriesRfqMessage.encode message
  | .optionsNonDisplayedTradeMessage message => OptionsNonDisplayedTradeMessage.encode message
  | .optionsCrossTradeMessage message => OptionsCrossTradeMessage.encode message
  | .optionsTradeCancelMessage message => OptionsTradeCancelMessage.encode message
  | .optionsOutrightSeriesSummaryMessage message => OptionsOutrightSeriesSummaryMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 524289 := by
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
  | outrightSeriesIndexMappingMessage inner =>
    simp only [encode, OutrightSeriesIndexMappingMessage.encode_length]
    omega
  | optionsStatusMessage inner =>
    simp only [encode, OptionsStatusMessage.encode_length]
    omega
  | complexSeriesIndexMappingMessage inner =>
    have bound_inner := ComplexSeriesIndexMappingMessage.encode_length_le inner
    simp only [encode]
    omega
  | retransmissionRequestMessage inner =>
    simp only [encode, RetransmissionRequestMessage.encode_length]
    omega
  | refreshHeaderMessage inner =>
    have bound_inner := RefreshHeaderMessage.encode_length_le inner
    simp only [encode]
    omega
  | refreshRequestMessage inner =>
    simp only [encode, RefreshRequestMessage.encode_length]
    omega
  | symbolIndexMappingRequestMessage inner =>
    simp only [encode, SymbolIndexMappingRequestMessage.encode_length]
    omega
  | messageUnavailableMessage inner =>
    simp only [encode, MessageUnavailableMessage.encode_length]
    omega
  | requestResponseMessage inner =>
    simp only [encode, RequestResponseMessage.encode_length]
    omega
  | heartbeatResponseMessage inner =>
    simp only [encode, HeartbeatResponseMessage.encode_length]
    omega
  | optionsAddOrderMessage inner =>
    simp only [encode, OptionsAddOrderMessage.encode_length]
    omega
  | optionsModifyOrderMessage inner =>
    simp only [encode, OptionsModifyOrderMessage.encode_length]
    omega
  | optionsDeleteOrderMessage inner =>
    simp only [encode, OptionsDeleteOrderMessage.encode_length]
    omega
  | optionsOrderExecutionMessage inner =>
    simp only [encode, OptionsOrderExecutionMessage.encode_length]
    omega
  | optionsReplaceOrderMessage inner =>
    simp only [encode, OptionsReplaceOrderMessage.encode_length]
    omega
  | optionsImbalanceMessage inner =>
    simp only [encode, OptionsImbalanceMessage.encode_length]
    omega
  | optionsAddOrderRefreshMessage inner =>
    simp only [encode, OptionsAddOrderRefreshMessage.encode_length]
    omega
  | optionsSeriesRfqMessage inner =>
    simp only [encode, OptionsSeriesRfqMessage.encode_length]
    omega
  | optionsNonDisplayedTradeMessage inner =>
    simp only [encode, OptionsNonDisplayedTradeMessage.encode_length]
    omega
  | optionsCrossTradeMessage inner =>
    simp only [encode, OptionsCrossTradeMessage.encode_length]
    omega
  | optionsTradeCancelMessage inner =>
    simp only [encode, OptionsTradeCancelMessage.encode_length]
    omega
  | optionsOutrightSeriesSummaryMessage inner =>
    simp only [encode, OptionsOutrightSeriesSummaryMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (SequenceNumberResetMessage.decode bytes).map fun (message, rest) => (.sequenceNumberResetMessage message, rest)
  else if tag = 2 then (SourceTimeReferenceMessage.decode bytes).map fun (message, rest) => (.sourceTimeReferenceMessage message, rest)
  else if tag = 3 then (SymbolIndexMappingMessage.decode bytes).map fun (message, rest) => (.symbolIndexMappingMessage message, rest)
  else if tag = 32 then (SymbolClearMessage.decode bytes).map fun (message, rest) => (.symbolClearMessage message, rest)
  else if tag = 34 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 50 then (OutrightSeriesIndexMappingMessage.decode bytes).map fun (message, rest) => (.outrightSeriesIndexMappingMessage message, rest)
  else if tag = 51 then (OptionsStatusMessage.decode bytes).map fun (message, rest) => (.optionsStatusMessage message, rest)
  else if tag = 60 then (ComplexSeriesIndexMappingMessage.decode bytes).map fun (message, rest) => (.complexSeriesIndexMappingMessage message, rest)
  else if tag = 10 then (RetransmissionRequestMessage.decode bytes).map fun (message, rest) => (.retransmissionRequestMessage message, rest)
  else if tag = 35 then (RefreshHeaderMessage.decode bytes).map fun (message, rest) => (.refreshHeaderMessage message, rest)
  else if tag = 15 then (RefreshRequestMessage.decode bytes).map fun (message, rest) => (.refreshRequestMessage message, rest)
  else if tag = 13 then (SymbolIndexMappingRequestMessage.decode bytes).map fun (message, rest) => (.symbolIndexMappingRequestMessage message, rest)
  else if tag = 31 then (MessageUnavailableMessage.decode bytes).map fun (message, rest) => (.messageUnavailableMessage message, rest)
  else if tag = 11 then (RequestResponseMessage.decode bytes).map fun (message, rest) => (.requestResponseMessage message, rest)
  else if tag = 12 then (HeartbeatResponseMessage.decode bytes).map fun (message, rest) => (.heartbeatResponseMessage message, rest)
  else if tag = 300 then (OptionsAddOrderMessage.decode bytes).map fun (message, rest) => (.optionsAddOrderMessage message, rest)
  else if tag = 301 then (OptionsModifyOrderMessage.decode bytes).map fun (message, rest) => (.optionsModifyOrderMessage message, rest)
  else if tag = 302 then (OptionsDeleteOrderMessage.decode bytes).map fun (message, rest) => (.optionsDeleteOrderMessage message, rest)
  else if tag = 303 then (OptionsOrderExecutionMessage.decode bytes).map fun (message, rest) => (.optionsOrderExecutionMessage message, rest)
  else if tag = 304 then (OptionsReplaceOrderMessage.decode bytes).map fun (message, rest) => (.optionsReplaceOrderMessage message, rest)
  else if tag = 305 then (OptionsImbalanceMessage.decode bytes).map fun (message, rest) => (.optionsImbalanceMessage message, rest)
  else if tag = 306 then (OptionsAddOrderRefreshMessage.decode bytes).map fun (message, rest) => (.optionsAddOrderRefreshMessage message, rest)
  else if tag = 307 then (OptionsSeriesRfqMessage.decode bytes).map fun (message, rest) => (.optionsSeriesRfqMessage message, rest)
  else if tag = 310 then (OptionsNonDisplayedTradeMessage.decode bytes).map fun (message, rest) => (.optionsNonDisplayedTradeMessage message, rest)
  else if tag = 311 then (OptionsCrossTradeMessage.decode bytes).map fun (message, rest) => (.optionsCrossTradeMessage message, rest)
  else if tag = 312 then (OptionsTradeCancelMessage.decode bytes).map fun (message, rest) => (.optionsTradeCancelMessage message, rest)
  else if tag = 323 then (OptionsOutrightSeriesSummaryMessage.decode bytes).map fun (message, rest) => (.optionsOutrightSeriesSummaryMessage message, rest)
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

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  pktSize : BitVec 16
  deliveryFlag : BitVec 8
  seqNum : BitVec 32
  sendTime : SendTime
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.pktSize
    ++ (encodeUIntLE 1 message.deliveryFlag
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUIntLE 4 message.seqNum
    ++ (SendTime.encode message.sendTime
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (pktSize, bytes) ← decodeUIntLE 2 bytes
  let (deliveryFlag, bytes) ← decodeUIntLE 1 bytes
  let (numberMsgs, bytes) ← decodeUIntLE 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← SendTime.decode bytes
  let (message_, bytes) ← decodeMany Message.decode numberMsgs.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ pktSize, deliveryFlag, seqNum, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
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

end Omi.NyseArcaoptionsDeepfeedPillarV12M
