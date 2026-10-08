import Wire

/-!
# The Securities Industry Automation Corporation  v2.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.SiacCqsSnapshotCtaV21

/-- Participant Id: one byte code -/
def ParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive ParticipantId where
  | nyseAmerican -- Nyse American
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nyseNational -- Nyse National
  | finraAdf -- Finra Adf
  | n24X -- N 24 X
  | miax -- Miax
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseTexas -- Nyse Texas
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | cqs -- Cqs
  | nasdaq -- Nasdaq
  | memx -- Memx
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqOmxPsx -- Nasdaq Omx Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | unlisted (byte : { byte : UInt8 // byte ∉ ParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ParticipantId

def toByte : ParticipantId → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqOmxBx => 0x42
  | .nyseNational => 0x43
  | .finraAdf => 0x44
  | .n24X => 0x47
  | .miax => 0x48
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseTexas => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .cqs => 0x53
  | .nasdaq => 0x54
  | .memx => 0x55
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqOmxPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ParticipantId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqOmxBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finraAdf
  else if byte = 0x47 then .n24X
  else if byte = 0x48 then .miax
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x53 then .cqs
  else if byte = 0x54 then .nasdaq
  else if byte = 0x55 then .memx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqOmxPsx
  else if byte = 0x59 then .cboeByx
  else .cboeBzx

def ofByte (byte : UInt8) : ParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ParticipantId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqOmxBx => decide
  | nyseNational => decide
  | finraAdf => decide
  | n24X => decide
  | miax => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseTexas => decide
  | nyse => decide
  | nyseArca => decide
  | cqs => decide
  | nasdaq => decide
  | memx => decide
  | iex => decide
  | cbsx => decide
  | nasdaqOmxPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ParticipantId

/-- Primary Listing Market Participant Id: one byte code -/
def PrimaryListingMarketParticipantId.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive PrimaryListingMarketParticipantId where
  | primaryListingMarketParticipantIdNotApplicable -- Primary Listing Market Participant Id Not Applicable
  | nyseAmerican -- Nyse American
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nyseNational -- Nyse National
  | finraAdf -- Finra Adf
  | n24X -- N 24 X
  | miaxPearl -- Miax Pearl
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseTexas -- Nyse Texas
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | membersExchange -- Members Exchange
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqOmxPsx -- Nasdaq Omx Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | unlisted (byte : { byte : UInt8 // byte ∉ PrimaryListingMarketParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrimaryListingMarketParticipantId

def toByte : PrimaryListingMarketParticipantId → UInt8
  | .primaryListingMarketParticipantIdNotApplicable => 0x20
  | .nyseAmerican => 0x41
  | .nasdaqOmxBx => 0x42
  | .nyseNational => 0x43
  | .finraAdf => 0x44
  | .n24X => 0x47
  | .miaxPearl => 0x48
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseTexas => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x54
  | .membersExchange => 0x55
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqOmxPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrimaryListingMarketParticipantId :=
  if byte = 0x20 then .primaryListingMarketParticipantIdNotApplicable
  else if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqOmxBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finraAdf
  else if byte = 0x47 then .n24X
  else if byte = 0x48 then .miaxPearl
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x54 then .nasdaq
  else if byte = 0x55 then .membersExchange
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqOmxPsx
  else if byte = 0x59 then .cboeByx
  else .cboeBzx

def ofByte (byte : UInt8) : PrimaryListingMarketParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrimaryListingMarketParticipantId) : ofByte value.toByte = value := by
  cases value with
  | primaryListingMarketParticipantIdNotApplicable => decide
  | nyseAmerican => decide
  | nasdaqOmxBx => decide
  | nyseNational => decide
  | finraAdf => decide
  | n24X => decide
  | miaxPearl => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseTexas => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | membersExchange => decide
  | iex => decide
  | cbsx => decide
  | nasdaqOmxPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrimaryListingMarketParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrimaryListingMarketParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrimaryListingMarketParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrimaryListingMarketParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrimaryListingMarketParticipantId

/-- Luld Tier: one byte code -/
def LuldTier.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive LuldTier where
  | luldNotApplicable -- Luld Not Applicable
  | luldTier1Security -- Luld Tier 1 Security
  | luldTier2Security -- Luld Tier 2 Security
  | unlisted (byte : { byte : UInt8 // byte ∉ LuldTier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LuldTier

def toByte : LuldTier → UInt8
  | .luldNotApplicable => 0x30
  | .luldTier1Security => 0x31
  | .luldTier2Security => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LuldTier :=
  if byte = 0x30 then .luldNotApplicable
  else if byte = 0x31 then .luldTier1Security
  else .luldTier2Security

def ofByte (byte : UInt8) : LuldTier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LuldTier) : ofByte value.toByte = value := by
  cases value with
  | luldNotApplicable => decide
  | luldTier1Security => decide
  | luldTier2Security => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LuldTier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LuldTier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LuldTier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LuldTier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LuldTier

/-- Test: one byte code -/
def Test.codes : List UInt8 :=
  [0x30, 0x31]

inductive Test where
  | notATestSymbol -- Not A Test Symbol
  | testSymbol -- Test Symbol
  | unlisted (byte : { byte : UInt8 // byte ∉ Test.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Test

def toByte : Test → UInt8
  | .notATestSymbol => 0x30
  | .testSymbol => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Test :=
  if byte = 0x30 then .notATestSymbol
  else .testSymbol

def ofByte (byte : UInt8) : Test :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Test) : ofByte value.toByte = value := by
  cases value with
  | notATestSymbol => decide
  | testSymbol => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Test) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Test × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Test) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Test) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Test

/-- Ipo: one byte code -/
def Ipo.codes : List UInt8 :=
  [0x30, 0x31]

inductive Ipo where
  | notAnIpoSymbol -- Not An Ipo Symbol
  | ipoSymbol -- Ipo Symbol
  | unlisted (byte : { byte : UInt8 // byte ∉ Ipo.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Ipo

def toByte : Ipo → UInt8
  | .notAnIpoSymbol => 0x30
  | .ipoSymbol => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Ipo :=
  if byte = 0x30 then .notAnIpoSymbol
  else .ipoSymbol

def ofByte (byte : UInt8) : Ipo :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Ipo) : ofByte value.toByte = value := by
  cases value with
  | notAnIpoSymbol => decide
  | ipoSymbol => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Ipo) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Ipo × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Ipo) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Ipo) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Ipo

/-- Financial Status Indicator: one byte code -/
def FinancialStatusIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41]

inductive FinancialStatusIndicator where
  | financialStatusNotApplicable -- Financial Status Not Applicable
  | bankrupt -- Bankrupt
  | belowContinuingListingStandards -- Below Continuing Listing Standards
  | bankruptAndBelowContinuingListingStandards -- Bankrupt And Below Continuing Listing Standards
  | lateFiling -- Late Filing
  | bankruptAndLateFiling -- Bankrupt And Late Filing
  | belowContinuingListingStandardsAndLateFiling -- Below Continuing Listing Standards And Late Filing
  | bankruptBelowContinuingListingStandardsAndLateFiling -- Bankrupt Below Continuing Listing Standards And Late Filing
  | creationsSuspended -- Creations Suspended
  | redemptionsSuspended -- Redemptions Suspended
  | liquidation -- Liquidation
  | unlisted (byte : { byte : UInt8 // byte ∉ FinancialStatusIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinancialStatusIndicator

def toByte : FinancialStatusIndicator → UInt8
  | .financialStatusNotApplicable => 0x30
  | .bankrupt => 0x31
  | .belowContinuingListingStandards => 0x32
  | .bankruptAndBelowContinuingListingStandards => 0x33
  | .lateFiling => 0x34
  | .bankruptAndLateFiling => 0x35
  | .belowContinuingListingStandardsAndLateFiling => 0x36
  | .bankruptBelowContinuingListingStandardsAndLateFiling => 0x37
  | .creationsSuspended => 0x38
  | .redemptionsSuspended => 0x39
  | .liquidation => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinancialStatusIndicator :=
  if byte = 0x30 then .financialStatusNotApplicable
  else if byte = 0x31 then .bankrupt
  else if byte = 0x32 then .belowContinuingListingStandards
  else if byte = 0x33 then .bankruptAndBelowContinuingListingStandards
  else if byte = 0x34 then .lateFiling
  else if byte = 0x35 then .bankruptAndLateFiling
  else if byte = 0x36 then .belowContinuingListingStandardsAndLateFiling
  else if byte = 0x37 then .bankruptBelowContinuingListingStandardsAndLateFiling
  else if byte = 0x38 then .creationsSuspended
  else if byte = 0x39 then .redemptionsSuspended
  else .liquidation

def ofByte (byte : UInt8) : FinancialStatusIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinancialStatusIndicator) : ofByte value.toByte = value := by
  cases value with
  | financialStatusNotApplicable => decide
  | bankrupt => decide
  | belowContinuingListingStandards => decide
  | bankruptAndBelowContinuingListingStandards => decide
  | lateFiling => decide
  | bankruptAndLateFiling => decide
  | belowContinuingListingStandardsAndLateFiling => decide
  | bankruptBelowContinuingListingStandardsAndLateFiling => decide
  | creationsSuspended => decide
  | redemptionsSuspended => decide
  | liquidation => decide
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

/-- Short Sale Restriction Indicator: one byte code -/
def ShortSaleRestrictionIndicator.codes : List UInt8 :=
  [0x20, 0x45]

inductive ShortSaleRestrictionIndicator where
  | shortSaleRestrictionNotInEffect -- Short Sale Restriction Not In Effect
  | shortSaleRestrictionInEffect -- Short Sale Restriction In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSaleRestrictionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSaleRestrictionIndicator

def toByte : ShortSaleRestrictionIndicator → UInt8
  | .shortSaleRestrictionNotInEffect => 0x20
  | .shortSaleRestrictionInEffect => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSaleRestrictionIndicator :=
  if byte = 0x20 then .shortSaleRestrictionNotInEffect
  else .shortSaleRestrictionInEffect

def ofByte (byte : UInt8) : ShortSaleRestrictionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSaleRestrictionIndicator) : ofByte value.toByte = value := by
  cases value with
  | shortSaleRestrictionNotInEffect => decide
  | shortSaleRestrictionInEffect => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSaleRestrictionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSaleRestrictionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSaleRestrictionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ShortSaleRestrictionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSaleRestrictionIndicator

/-- Halt Reason: one byte code -/
def HaltReason.codes : List UInt8 :=
  [0x20, 0x41, 0x43, 0x44, 0x45, 0x46, 0x49, 0x4D, 0x4E, 0x4F, 0x50, 0x56, 0x58, 0x59, 0x31, 0x32, 0x33]

inductive HaltReason where
  | haltReasonNotApplicable -- Halt Reason Not Applicable
  | additionalInformationRequested -- Additional Information Requested
  | regulatoryConcern -- Regulatory Concern
  | newsReleased -- News Released
  | mergerEffective -- Merger Effective
  | etfComponentPricesNotAvailable -- Etf Component Prices Not Available
  | orderImbalance -- Order Imbalance
  | limitUpLimitDownLuldTradingPause -- Limit Up Limit Down Luld Trading Pause
  | corporateAction -- Corporate Action
  | newSecurityOffering -- New Security Offering
  | newsPending -- News Pending
  | intradayIndicativeValueNotAvailable -- Intraday Indicative Value Not Available
  | operational -- Operational
  | subPennyTrading -- Sub Penny Trading
  | marketWideCircuitBreakerLevel1Breached -- Market Wide Circuit Breaker Level 1 Breached
  | marketWideCircuitBreakerLevel2Breached -- Market Wide Circuit Breaker Level 2 Breached
  | marketWideCircuitBreakerLevel3Breached -- Market Wide Circuit Breaker Level 3 Breached
  | unlisted (byte : { byte : UInt8 // byte ∉ HaltReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HaltReason

def toByte : HaltReason → UInt8
  | .haltReasonNotApplicable => 0x20
  | .additionalInformationRequested => 0x41
  | .regulatoryConcern => 0x43
  | .newsReleased => 0x44
  | .mergerEffective => 0x45
  | .etfComponentPricesNotAvailable => 0x46
  | .orderImbalance => 0x49
  | .limitUpLimitDownLuldTradingPause => 0x4D
  | .corporateAction => 0x4E
  | .newSecurityOffering => 0x4F
  | .newsPending => 0x50
  | .intradayIndicativeValueNotAvailable => 0x56
  | .operational => 0x58
  | .subPennyTrading => 0x59
  | .marketWideCircuitBreakerLevel1Breached => 0x31
  | .marketWideCircuitBreakerLevel2Breached => 0x32
  | .marketWideCircuitBreakerLevel3Breached => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HaltReason :=
  if byte = 0x20 then .haltReasonNotApplicable
  else if byte = 0x41 then .additionalInformationRequested
  else if byte = 0x43 then .regulatoryConcern
  else if byte = 0x44 then .newsReleased
  else if byte = 0x45 then .mergerEffective
  else if byte = 0x46 then .etfComponentPricesNotAvailable
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x4D then .limitUpLimitDownLuldTradingPause
  else if byte = 0x4E then .corporateAction
  else if byte = 0x4F then .newSecurityOffering
  else if byte = 0x50 then .newsPending
  else if byte = 0x56 then .intradayIndicativeValueNotAvailable
  else if byte = 0x58 then .operational
  else if byte = 0x59 then .subPennyTrading
  else if byte = 0x31 then .marketWideCircuitBreakerLevel1Breached
  else if byte = 0x32 then .marketWideCircuitBreakerLevel2Breached
  else .marketWideCircuitBreakerLevel3Breached

def ofByte (byte : UInt8) : HaltReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HaltReason) : ofByte value.toByte = value := by
  cases value with
  | haltReasonNotApplicable => decide
  | additionalInformationRequested => decide
  | regulatoryConcern => decide
  | newsReleased => decide
  | mergerEffective => decide
  | etfComponentPricesNotAvailable => decide
  | orderImbalance => decide
  | limitUpLimitDownLuldTradingPause => decide
  | corporateAction => decide
  | newSecurityOffering => decide
  | newsPending => decide
  | intradayIndicativeValueNotAvailable => decide
  | operational => decide
  | subPennyTrading => decide
  | marketWideCircuitBreakerLevel1Breached => decide
  | marketWideCircuitBreakerLevel2Breached => decide
  | marketWideCircuitBreakerLevel3Breached => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HaltReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HaltReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HaltReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : HaltReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HaltReason

/-- Instrument Type: one byte code -/
def InstrumentType.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33]

inductive InstrumentType where
  | ctaEligibleEquity -- Cta Eligible Equity
  | localIssue -- Local Issue
  | corporateBond -- Corporate Bond
  | governmentBond -- Government Bond
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .ctaEligibleEquity => 0x30
  | .localIssue => 0x31
  | .corporateBond => 0x32
  | .governmentBond => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentType :=
  if byte = 0x30 then .ctaEligibleEquity
  else if byte = 0x31 then .localIssue
  else if byte = 0x32 then .corporateBond
  else .governmentBond

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | ctaEligibleEquity => decide
  | localIssue => decide
  | corporateBond => decide
  | governmentBond => decide
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

/-- National Bbo Luld Indicator: one byte code -/
def NationalBboLuldIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49]

inductive NationalBboLuldIndicator where
  | limitUpLimitDownNotApplicable -- Limit Up Limit Down Not Applicable
  | nationalBestBidAndorNationalBestOfferAreExecutable -- National Best Bid Andor National Best Offer Are Executable
  | nationalBestBidBelowLowerLimitPriceBand -- National Best Bid Below Lower Limit Price Band
  | nationalBestOfferAboveUpperLimitPriceBand -- National Best Offer Above Upper Limit Price Band
  | nationalBestBidBelowLowerLimitPriceBandAndNationalBestOfferAboveUpperLimitPriceBand -- National Best Bid Below Lower Limit Price Band And National Best Offer Above Upper Limit Price Band
  | nationalBestBidEqualsUpperLimitPriceBand -- National Best Bid Equals Upper Limit Price Band
  | nationalBestOfferEqualsLowerLimitPriceBand -- National Best Offer Equals Lower Limit Price Band
  | nationalBestBidEqualsUpperLimitPriceBandAndNationalBestOfferAboveUpperLimitPriceBand -- National Best Bid Equals Upper Limit Price Band And National Best Offer Above Upper Limit Price Band
  | nationalBestBidBelowLowerLimitPriceBandAndNationalBestOfferEqualsLowerLimitPriceBand -- National Best Bid Below Lower Limit Price Band And National Best Offer Equals Lower Limit Price Band
  | nationalBestBidEqualsUpperLimitPriceBandAndNationalBestOfferEqualsLowerLimitPriceBand -- National Best Bid Equals Upper Limit Price Band And National Best Offer Equals Lower Limit Price Band
  | unlisted (byte : { byte : UInt8 // byte ∉ NationalBboLuldIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NationalBboLuldIndicator

def toByte : NationalBboLuldIndicator → UInt8
  | .limitUpLimitDownNotApplicable => 0x20
  | .nationalBestBidAndorNationalBestOfferAreExecutable => 0x41
  | .nationalBestBidBelowLowerLimitPriceBand => 0x42
  | .nationalBestOfferAboveUpperLimitPriceBand => 0x43
  | .nationalBestBidBelowLowerLimitPriceBandAndNationalBestOfferAboveUpperLimitPriceBand => 0x44
  | .nationalBestBidEqualsUpperLimitPriceBand => 0x45
  | .nationalBestOfferEqualsLowerLimitPriceBand => 0x46
  | .nationalBestBidEqualsUpperLimitPriceBandAndNationalBestOfferAboveUpperLimitPriceBand => 0x47
  | .nationalBestBidBelowLowerLimitPriceBandAndNationalBestOfferEqualsLowerLimitPriceBand => 0x48
  | .nationalBestBidEqualsUpperLimitPriceBandAndNationalBestOfferEqualsLowerLimitPriceBand => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NationalBboLuldIndicator :=
  if byte = 0x20 then .limitUpLimitDownNotApplicable
  else if byte = 0x41 then .nationalBestBidAndorNationalBestOfferAreExecutable
  else if byte = 0x42 then .nationalBestBidBelowLowerLimitPriceBand
  else if byte = 0x43 then .nationalBestOfferAboveUpperLimitPriceBand
  else if byte = 0x44 then .nationalBestBidBelowLowerLimitPriceBandAndNationalBestOfferAboveUpperLimitPriceBand
  else if byte = 0x45 then .nationalBestBidEqualsUpperLimitPriceBand
  else if byte = 0x46 then .nationalBestOfferEqualsLowerLimitPriceBand
  else if byte = 0x47 then .nationalBestBidEqualsUpperLimitPriceBandAndNationalBestOfferAboveUpperLimitPriceBand
  else if byte = 0x48 then .nationalBestBidBelowLowerLimitPriceBandAndNationalBestOfferEqualsLowerLimitPriceBand
  else .nationalBestBidEqualsUpperLimitPriceBandAndNationalBestOfferEqualsLowerLimitPriceBand

def ofByte (byte : UInt8) : NationalBboLuldIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NationalBboLuldIndicator) : ofByte value.toByte = value := by
  cases value with
  | limitUpLimitDownNotApplicable => decide
  | nationalBestBidAndorNationalBestOfferAreExecutable => decide
  | nationalBestBidBelowLowerLimitPriceBand => decide
  | nationalBestOfferAboveUpperLimitPriceBand => decide
  | nationalBestBidBelowLowerLimitPriceBandAndNationalBestOfferAboveUpperLimitPriceBand => decide
  | nationalBestBidEqualsUpperLimitPriceBand => decide
  | nationalBestOfferEqualsLowerLimitPriceBand => decide
  | nationalBestBidEqualsUpperLimitPriceBandAndNationalBestOfferAboveUpperLimitPriceBand => decide
  | nationalBestBidBelowLowerLimitPriceBandAndNationalBestOfferEqualsLowerLimitPriceBand => decide
  | nationalBestBidEqualsUpperLimitPriceBandAndNationalBestOfferEqualsLowerLimitPriceBand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NationalBboLuldIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NationalBboLuldIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NationalBboLuldIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NationalBboLuldIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NationalBboLuldIndicator

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x45, 0x46, 0x48, 0x4C, 0x4E, 0x4F, 0x52, 0x55, 0x57, 0x34]

inductive QuoteCondition where
  | quoteConditionNotApplicable -- Quote Condition Not Applicable
  | slowQuoteOnOfferSide -- Slow Quote On Offer Side
  | slowQuoteOnBidSide -- Slow Quote On Bid Side
  | closing -- Closing
  | slowQuoteDueToLrpOrGapQuoteOnTheBidSide -- Slow Quote Due To Lrp Or Gap Quote On The Bid Side
  | slowQuoteDueToLrpOrGapQuoteOnTheOfferSide -- Slow Quote Due To Lrp Or Gap Quote On The Offer Side
  | slowQuoteOnTheBidAndOfferSides -- Slow Quote On The Bid And Offer Sides
  | closedMarketMakerFinra -- Closed Market Maker Finra
  | nonFirmQuote -- Non Firm Quote
  | openingQuote -- Opening Quote
  | regularFinraOpen -- Regular Finra Open
  | slowQuoteDueToLrpOrGapQuoteOnBothTheBidAndOfferSides -- Slow Quote Due To Lrp Or Gap Quote On Both The Bid And Offer Sides
  | slowQuoteDueToSetSlowListOnBothTheBidAndOfferSides -- Slow Quote Due To Set Slow List On Both The Bid And Offer Sides
  | onDemandIntraDayAuction -- On Demand Intra Day Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .quoteConditionNotApplicable => 0x20
  | .slowQuoteOnOfferSide => 0x41
  | .slowQuoteOnBidSide => 0x42
  | .closing => 0x43
  | .slowQuoteDueToLrpOrGapQuoteOnTheBidSide => 0x45
  | .slowQuoteDueToLrpOrGapQuoteOnTheOfferSide => 0x46
  | .slowQuoteOnTheBidAndOfferSides => 0x48
  | .closedMarketMakerFinra => 0x4C
  | .nonFirmQuote => 0x4E
  | .openingQuote => 0x4F
  | .regularFinraOpen => 0x52
  | .slowQuoteDueToLrpOrGapQuoteOnBothTheBidAndOfferSides => 0x55
  | .slowQuoteDueToSetSlowListOnBothTheBidAndOfferSides => 0x57
  | .onDemandIntraDayAuction => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x20 then .quoteConditionNotApplicable
  else if byte = 0x41 then .slowQuoteOnOfferSide
  else if byte = 0x42 then .slowQuoteOnBidSide
  else if byte = 0x43 then .closing
  else if byte = 0x45 then .slowQuoteDueToLrpOrGapQuoteOnTheBidSide
  else if byte = 0x46 then .slowQuoteDueToLrpOrGapQuoteOnTheOfferSide
  else if byte = 0x48 then .slowQuoteOnTheBidAndOfferSides
  else if byte = 0x4C then .closedMarketMakerFinra
  else if byte = 0x4E then .nonFirmQuote
  else if byte = 0x4F then .openingQuote
  else if byte = 0x52 then .regularFinraOpen
  else if byte = 0x55 then .slowQuoteDueToLrpOrGapQuoteOnBothTheBidAndOfferSides
  else if byte = 0x57 then .slowQuoteDueToSetSlowListOnBothTheBidAndOfferSides
  else .onDemandIntraDayAuction

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | quoteConditionNotApplicable => decide
  | slowQuoteOnOfferSide => decide
  | slowQuoteOnBidSide => decide
  | closing => decide
  | slowQuoteDueToLrpOrGapQuoteOnTheBidSide => decide
  | slowQuoteDueToLrpOrGapQuoteOnTheOfferSide => decide
  | slowQuoteOnTheBidAndOfferSides => decide
  | closedMarketMakerFinra => decide
  | nonFirmQuote => decide
  | openingQuote => decide
  | regularFinraOpen => decide
  | slowQuoteDueToLrpOrGapQuoteOnBothTheBidAndOfferSides => decide
  | slowQuoteDueToSetSlowListOnBothTheBidAndOfferSides => decide
  | onDemandIntraDayAuction => decide
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

/-- Retail Interest Indicator: one byte code -/
def RetailInterestIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43]

inductive RetailInterestIndicator where
  | retailInterestIndicatorNotApplicable -- Retail Interest Indicator Not Applicable
  | retailInterestOnBidQuote -- Retail Interest On Bid Quote
  | retailInterestOnOfferQuote -- Retail Interest On Offer Quote
  | retailInterestOnBothTheBidAndOfferQuotes -- Retail Interest On Both The Bid And Offer Quotes
  | unlisted (byte : { byte : UInt8 // byte ∉ RetailInterestIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetailInterestIndicator

def toByte : RetailInterestIndicator → UInt8
  | .retailInterestIndicatorNotApplicable => 0x20
  | .retailInterestOnBidQuote => 0x41
  | .retailInterestOnOfferQuote => 0x42
  | .retailInterestOnBothTheBidAndOfferQuotes => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RetailInterestIndicator :=
  if byte = 0x20 then .retailInterestIndicatorNotApplicable
  else if byte = 0x41 then .retailInterestOnBidQuote
  else if byte = 0x42 then .retailInterestOnOfferQuote
  else .retailInterestOnBothTheBidAndOfferQuotes

def ofByte (byte : UInt8) : RetailInterestIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetailInterestIndicator) : ofByte value.toByte = value := by
  cases value with
  | retailInterestIndicatorNotApplicable => decide
  | retailInterestOnBidQuote => decide
  | retailInterestOnOfferQuote => decide
  | retailInterestOnBothTheBidAndOfferQuotes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RetailInterestIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetailInterestIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RetailInterestIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RetailInterestIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RetailInterestIndicator

/-- Settlement Condition: one byte code -/
def SettlementCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42]

inductive SettlementCondition where
  | regularWaySettlement -- Regular Way Settlement
  | cashOnlySettlement -- Cash Only Settlement
  | nextDayOnlySettlement -- Next Day Only Settlement
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementCondition

def toByte : SettlementCondition → UInt8
  | .regularWaySettlement => 0x20
  | .cashOnlySettlement => 0x41
  | .nextDayOnlySettlement => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementCondition :=
  if byte = 0x20 then .regularWaySettlement
  else if byte = 0x41 then .cashOnlySettlement
  else .nextDayOnlySettlement

def ofByte (byte : UInt8) : SettlementCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementCondition) : ofByte value.toByte = value := by
  cases value with
  | regularWaySettlement => decide
  | cashOnlySettlement => decide
  | nextDayOnlySettlement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlementCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementCondition

/-- Market Condition: one byte code -/
def MarketCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42]

inductive MarketCondition where
  | normalAuctionMarket -- Normal Auction Market
  | crossedMarket -- Crossed Market
  | lockedMarket -- Locked Market
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCondition

def toByte : MarketCondition → UInt8
  | .normalAuctionMarket => 0x20
  | .crossedMarket => 0x41
  | .lockedMarket => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCondition :=
  if byte = 0x20 then .normalAuctionMarket
  else if byte = 0x41 then .crossedMarket
  else .lockedMarket

def ofByte (byte : UInt8) : MarketCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCondition) : ofByte value.toByte = value := by
  cases value with
  | normalAuctionMarket => decide
  | crossedMarket => decide
  | lockedMarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCondition

/-- Limit Up Limit Down Luld Indicator: one byte code -/
def LimitUpLimitDownLuldIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42]

inductive LimitUpLimitDownLuldIndicator where
  | limitUpLimitDownNotApplicable -- Limit Up Limit Down Not Applicable
  | bidPriceAboveUpperLimitPriceBand -- Bid Price Above Upper Limit Price Band
  | offerPriceBelowLowerLimitPriceBand -- Offer Price Below Lower Limit Price Band
  | unlisted (byte : { byte : UInt8 // byte ∉ LimitUpLimitDownLuldIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LimitUpLimitDownLuldIndicator

def toByte : LimitUpLimitDownLuldIndicator → UInt8
  | .limitUpLimitDownNotApplicable => 0x20
  | .bidPriceAboveUpperLimitPriceBand => 0x41
  | .offerPriceBelowLowerLimitPriceBand => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LimitUpLimitDownLuldIndicator :=
  if byte = 0x20 then .limitUpLimitDownNotApplicable
  else if byte = 0x41 then .bidPriceAboveUpperLimitPriceBand
  else .offerPriceBelowLowerLimitPriceBand

def ofByte (byte : UInt8) : LimitUpLimitDownLuldIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LimitUpLimitDownLuldIndicator) : ofByte value.toByte = value := by
  cases value with
  | limitUpLimitDownNotApplicable => decide
  | bidPriceAboveUpperLimitPriceBand => decide
  | offerPriceBelowLowerLimitPriceBand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LimitUpLimitDownLuldIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LimitUpLimitDownLuldIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LimitUpLimitDownLuldIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LimitUpLimitDownLuldIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LimitUpLimitDownLuldIndicator

/-- Finra Bbo Luld Indicator: one byte code -/
def FinraBboLuldIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44]

inductive FinraBboLuldIndicator where
  | limitUpLimitDownNotApplicable -- Limit Up Limit Down Not Applicable
  | finraBestBidAndorFinraBestOfferAreExecutable -- Finra Best Bid Andor Finra Best Offer Are Executable
  | finraBestBidOutsidePriceBand -- Finra Best Bid Outside Price Band
  | finraBestOfferOutsidePriceBand -- Finra Best Offer Outside Price Band
  | finraBestBidAndFinraBestOfferOutsidePriceBand -- Finra Best Bid And Finra Best Offer Outside Price Band
  | unlisted (byte : { byte : UInt8 // byte ∉ FinraBboLuldIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinraBboLuldIndicator

def toByte : FinraBboLuldIndicator → UInt8
  | .limitUpLimitDownNotApplicable => 0x20
  | .finraBestBidAndorFinraBestOfferAreExecutable => 0x41
  | .finraBestBidOutsidePriceBand => 0x42
  | .finraBestOfferOutsidePriceBand => 0x43
  | .finraBestBidAndFinraBestOfferOutsidePriceBand => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinraBboLuldIndicator :=
  if byte = 0x20 then .limitUpLimitDownNotApplicable
  else if byte = 0x41 then .finraBestBidAndorFinraBestOfferAreExecutable
  else if byte = 0x42 then .finraBestBidOutsidePriceBand
  else if byte = 0x43 then .finraBestOfferOutsidePriceBand
  else .finraBestBidAndFinraBestOfferOutsidePriceBand

def ofByte (byte : UInt8) : FinraBboLuldIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinraBboLuldIndicator) : ofByte value.toByte = value := by
  cases value with
  | limitUpLimitDownNotApplicable => decide
  | finraBestBidAndorFinraBestOfferAreExecutable => decide
  | finraBestBidOutsidePriceBand => decide
  | finraBestOfferOutsidePriceBand => decide
  | finraBestBidAndFinraBestOfferOutsidePriceBand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FinraBboLuldIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinraBboLuldIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FinraBboLuldIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FinraBboLuldIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FinraBboLuldIndicator

/-- Sip Block Timestamp: 8 bytes -/
structure SipBlockTimestamp where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace SipBlockTimestamp

def encode (message : SipBlockTimestamp) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (SipBlockTimestamp × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : SipBlockTimestamp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SipBlockTimestamp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SipBlockTimestamp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SipBlockTimestamp

/-- Line Integrity Message: 1 bytes -/
structure LineIntegrityMessage where
  participantId : ParticipantId
  deriving DecidableEq, Repr

namespace LineIntegrityMessage

def encode (message : LineIntegrityMessage) : List UInt8 :=
  ParticipantId.encode message.participantId

def decode (bytes : List UInt8) : Option (LineIntegrityMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  pure ({ participantId }, bytes)

@[simp] theorem encode_length (message : LineIntegrityMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [ParticipantId.encode_length]

theorem encode_length_pos (message : LineIntegrityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LineIntegrityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ParticipantId.decode_encode, some_bind]
  rfl

end LineIntegrityMessage

/-- Symbol Reference Data Message: 57 bytes -/
structure SymbolReferenceDataMessage where
  participantId : ParticipantId
  securitySymbol : Alpha 11
  priorSecuritySymbol : Alpha 11
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  primaryListingMarketPreviousClosingPrice : BitVec 64
  consolidatedClosingPrice : BitVec 64
  roundLotSize : BitVec 16
  reserved : Alpha 1
  luldTier : LuldTier
  luldLeverageRatio : BitVec 32
  test : Test
  ipo : Ipo
  financialStatusIndicator : FinancialStatusIndicator
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  haltReason : HaltReason
  instrumentType : InstrumentType
  secondReserved : Alpha 1
  thirdReserved : Alpha 1
  fourthReserved : Alpha 1
  deriving DecidableEq, Repr

namespace SymbolReferenceDataMessage

def encode (message : SymbolReferenceDataMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.priorSecuritySymbol
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (encodeUInt 8 message.primaryListingMarketPreviousClosingPrice
    ++ (encodeUInt 8 message.consolidatedClosingPrice
    ++ (encodeUInt 2 message.roundLotSize
    ++ (Alpha.encode message.reserved
    ++ (LuldTier.encode message.luldTier
    ++ (encodeUInt 4 message.luldLeverageRatio
    ++ (Test.encode message.test
    ++ (Ipo.encode message.ipo
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (HaltReason.encode message.haltReason
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.secondReserved
    ++ (Alpha.encode message.thirdReserved
    ++ (Alpha.encode message.fourthReserved))))))))))))))))))

def decode (bytes : List UInt8) : Option (SymbolReferenceDataMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (priorSecuritySymbol, bytes) ← Alpha.decode 11 bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (primaryListingMarketPreviousClosingPrice, bytes) ← decodeUInt 8 bytes
  let (consolidatedClosingPrice, bytes) ← decodeUInt 8 bytes
  let (roundLotSize, bytes) ← decodeUInt 2 bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (luldTier, bytes) ← LuldTier.decode bytes
  let (luldLeverageRatio, bytes) ← decodeUInt 4 bytes
  let (test, bytes) ← Test.decode bytes
  let (ipo, bytes) ← Ipo.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (haltReason, bytes) ← HaltReason.decode bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (secondReserved, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved, bytes) ← Alpha.decode 1 bytes
  pure ({ participantId, securitySymbol, priorSecuritySymbol, primaryListingMarketParticipantId, primaryListingMarketPreviousClosingPrice, consolidatedClosingPrice, roundLotSize, reserved, luldTier, luldLeverageRatio, test, ipo, financialStatusIndicator, shortSaleRestrictionIndicator, haltReason, instrumentType, secondReserved, thirdReserved, fourthReserved }, bytes)

@[simp] theorem encode_length (message : SymbolReferenceDataMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, encodeUInt_length, LuldTier.encode_length, Test.encode_length, Ipo.encode_length, FinancialStatusIndicator.encode_length, ShortSaleRestrictionIndicator.encode_length, HaltReason.encode_length, InstrumentType.encode_length]

theorem encode_length_pos (message : SymbolReferenceDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolReferenceDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LuldTier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Test.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Ipo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HaltReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolReferenceDataMessage

/-- Market Wide Circuit Breaker Decline Level Status Snapshot Message: 26 bytes -/
structure MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage where
  participantId : ParticipantId
  mwcbLevel1 : BitVec 64
  mwcbLevel2 : BitVec 64
  mwcbLevel3 : BitVec 64
  reserved : Alpha 1
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage

def encode (message : MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (encodeUInt 8 message.mwcbLevel1
    ++ (encodeUInt 8 message.mwcbLevel2
    ++ (encodeUInt 8 message.mwcbLevel3
    ++ (Alpha.encode message.reserved))))

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (mwcbLevel1, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel2, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel3, bytes) ← decodeUInt 8 bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  pure ({ participantId, mwcbLevel1, mwcbLevel2, mwcbLevel3, reserved }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage

/-- Consolidated Snapshot Message: 96 bytes -/
structure ConsolidatedSnapshotMessage where
  participantId : ParticipantId
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  lowerLimitPriceBand : BitVec 64
  upperLimitPriceBand : BitVec 64
  auctionCollarReferencePrice : BitVec 64
  auctionCollarUpperThresholdPrice : BitVec 64
  auctionCollarLowerThresholdPrice : BitVec 64
  numberOfExtensions : BitVec 8
  nationalBestBidParticipantId : Alpha 1
  nationalBestBidQuoteCondition : Alpha 1
  nationalBestBidPrice : BitVec 64
  nationalBestBidSize : BitVec 32
  finraBestBidMarketMakerId : Alpha 4
  nationalBestOfferParticipantId : Alpha 1
  nationalBestOfferQuoteCondition : Alpha 1
  nationalBestOfferPrice : BitVec 64
  nationalBestOfferSize : BitVec 32
  finraBestOfferMarketMakerId : Alpha 4
  nationalBboLuldIndicator : NationalBboLuldIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  haltReason : HaltReason
  reserved : Alpha 1
  deriving DecidableEq, Repr

namespace ConsolidatedSnapshotMessage

def encode (message : ConsolidatedSnapshotMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUInt 8 message.lowerLimitPriceBand
    ++ (encodeUInt 8 message.upperLimitPriceBand
    ++ (encodeUInt 8 message.auctionCollarReferencePrice
    ++ (encodeUInt 8 message.auctionCollarUpperThresholdPrice
    ++ (encodeUInt 8 message.auctionCollarLowerThresholdPrice
    ++ (encodeUInt 1 message.numberOfExtensions
    ++ (Alpha.encode message.nationalBestBidParticipantId
    ++ (Alpha.encode message.nationalBestBidQuoteCondition
    ++ (encodeUInt 8 message.nationalBestBidPrice
    ++ (encodeUInt 4 message.nationalBestBidSize
    ++ (Alpha.encode message.finraBestBidMarketMakerId
    ++ (Alpha.encode message.nationalBestOfferParticipantId
    ++ (Alpha.encode message.nationalBestOfferQuoteCondition
    ++ (encodeUInt 8 message.nationalBestOfferPrice
    ++ (encodeUInt 4 message.nationalBestOfferSize
    ++ (Alpha.encode message.finraBestOfferMarketMakerId
    ++ (NationalBboLuldIndicator.encode message.nationalBboLuldIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (HaltReason.encode message.haltReason
    ++ (Alpha.encode message.reserved))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ConsolidatedSnapshotMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (lowerLimitPriceBand, bytes) ← decodeUInt 8 bytes
  let (upperLimitPriceBand, bytes) ← decodeUInt 8 bytes
  let (auctionCollarReferencePrice, bytes) ← decodeUInt 8 bytes
  let (auctionCollarUpperThresholdPrice, bytes) ← decodeUInt 8 bytes
  let (auctionCollarLowerThresholdPrice, bytes) ← decodeUInt 8 bytes
  let (numberOfExtensions, bytes) ← decodeUInt 1 bytes
  let (nationalBestBidParticipantId, bytes) ← Alpha.decode 1 bytes
  let (nationalBestBidQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (nationalBestBidPrice, bytes) ← decodeUInt 8 bytes
  let (nationalBestBidSize, bytes) ← decodeUInt 4 bytes
  let (finraBestBidMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (nationalBestOfferParticipantId, bytes) ← Alpha.decode 1 bytes
  let (nationalBestOfferQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (nationalBestOfferPrice, bytes) ← decodeUInt 8 bytes
  let (nationalBestOfferSize, bytes) ← decodeUInt 4 bytes
  let (finraBestOfferMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (nationalBboLuldIndicator, bytes) ← NationalBboLuldIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (haltReason, bytes) ← HaltReason.decode bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  pure ({ participantId, securitySymbol, instrumentType, lowerLimitPriceBand, upperLimitPriceBand, auctionCollarReferencePrice, auctionCollarUpperThresholdPrice, auctionCollarLowerThresholdPrice, numberOfExtensions, nationalBestBidParticipantId, nationalBestBidQuoteCondition, nationalBestBidPrice, nationalBestBidSize, finraBestBidMarketMakerId, nationalBestOfferParticipantId, nationalBestOfferQuoteCondition, nationalBestOfferPrice, nationalBestOfferSize, finraBestOfferMarketMakerId, nationalBboLuldIndicator, primaryListingMarketParticipantId, financialStatusIndicator, shortSaleRestrictionIndicator, haltReason, reserved }, bytes)

@[simp] theorem encode_length (message : ConsolidatedSnapshotMessage) : (encode message).length = 96 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, NationalBboLuldIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, ShortSaleRestrictionIndicator.encode_length, HaltReason.encode_length]

theorem encode_length_pos (message : ConsolidatedSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ConsolidatedSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NationalBboLuldIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HaltReason.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ConsolidatedSnapshotMessage

/-- Participant Snapshot Message: 58 bytes -/
structure ParticipantSnapshotMessage where
  participantId : ParticipantId
  securitySymbol : Alpha 11
  quoteCondition : QuoteCondition
  bidPrice : BitVec 64
  bidSize : BitVec 32
  offerPrice : BitVec 64
  offerSize : BitVec 32
  retailInterestIndicator : RetailInterestIndicator
  settlementCondition : SettlementCondition
  marketCondition : MarketCondition
  limitUpLimitDownLuldIndicator : LimitUpLimitDownLuldIndicator
  highIndicationPrice : BitVec 64
  lowIndicationPrice : BitVec 64
  haltReason : HaltReason
  deriving DecidableEq, Repr

namespace ParticipantSnapshotMessage

def encode (message : ParticipantSnapshotMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Alpha.encode message.securitySymbol
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 8 message.bidPrice
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 8 message.offerPrice
    ++ (encodeUInt 4 message.offerSize
    ++ (RetailInterestIndicator.encode message.retailInterestIndicator
    ++ (SettlementCondition.encode message.settlementCondition
    ++ (MarketCondition.encode message.marketCondition
    ++ (LimitUpLimitDownLuldIndicator.encode message.limitUpLimitDownLuldIndicator
    ++ (encodeUInt 8 message.highIndicationPrice
    ++ (encodeUInt 8 message.lowIndicationPrice
    ++ (HaltReason.encode message.haltReason)))))))))))))

def decode (bytes : List UInt8) : Option (ParticipantSnapshotMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (bidPrice, bytes) ← decodeUInt 8 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (offerPrice, bytes) ← decodeUInt 8 bytes
  let (offerSize, bytes) ← decodeUInt 4 bytes
  let (retailInterestIndicator, bytes) ← RetailInterestIndicator.decode bytes
  let (settlementCondition, bytes) ← SettlementCondition.decode bytes
  let (marketCondition, bytes) ← MarketCondition.decode bytes
  let (limitUpLimitDownLuldIndicator, bytes) ← LimitUpLimitDownLuldIndicator.decode bytes
  let (highIndicationPrice, bytes) ← decodeUInt 8 bytes
  let (lowIndicationPrice, bytes) ← decodeUInt 8 bytes
  let (haltReason, bytes) ← HaltReason.decode bytes
  pure ({ participantId, securitySymbol, quoteCondition, bidPrice, bidSize, offerPrice, offerSize, retailInterestIndicator, settlementCondition, marketCondition, limitUpLimitDownLuldIndicator, highIndicationPrice, lowIndicationPrice, haltReason }, bytes)

@[simp] theorem encode_length (message : ParticipantSnapshotMessage) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Alpha.encode_length, QuoteCondition.encode_length, encodeUInt_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, LimitUpLimitDownLuldIndicator.encode_length, HaltReason.encode_length]

theorem encode_length_pos (message : ParticipantSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ParticipantSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RetailInterestIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LimitUpLimitDownLuldIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [HaltReason.decode_encode, some_bind]
  rfl

end ParticipantSnapshotMessage

/-- Finra Snapshot Message: 64 bytes -/
structure FinraSnapshotMessage where
  participantId : ParticipantId
  securitySymbol : Alpha 11
  finraBestBidQuoteCondition : Alpha 1
  finraBestBidPrice : BitVec 64
  finraBestBidSize : BitVec 32
  finraBestBidMarketMakerId : Alpha 4
  finraBestOfferQuoteCondition : Alpha 1
  finraBestOfferPrice : BitVec 64
  finraBestOfferSize : BitVec 32
  finraBestOfferMarketMakerId : Alpha 4
  finraBboLuldIndicator : FinraBboLuldIndicator
  highIndicationPrice : BitVec 64
  lowIndicationPrice : BitVec 64
  haltReason : HaltReason
  deriving DecidableEq, Repr

namespace FinraSnapshotMessage

def encode (message : FinraSnapshotMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.finraBestBidQuoteCondition
    ++ (encodeUInt 8 message.finraBestBidPrice
    ++ (encodeUInt 4 message.finraBestBidSize
    ++ (Alpha.encode message.finraBestBidMarketMakerId
    ++ (Alpha.encode message.finraBestOfferQuoteCondition
    ++ (encodeUInt 8 message.finraBestOfferPrice
    ++ (encodeUInt 4 message.finraBestOfferSize
    ++ (Alpha.encode message.finraBestOfferMarketMakerId
    ++ (FinraBboLuldIndicator.encode message.finraBboLuldIndicator
    ++ (encodeUInt 8 message.highIndicationPrice
    ++ (encodeUInt 8 message.lowIndicationPrice
    ++ (HaltReason.encode message.haltReason)))))))))))))

def decode (bytes : List UInt8) : Option (FinraSnapshotMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (finraBestBidQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (finraBestBidPrice, bytes) ← decodeUInt 8 bytes
  let (finraBestBidSize, bytes) ← decodeUInt 4 bytes
  let (finraBestBidMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBestOfferQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (finraBestOfferPrice, bytes) ← decodeUInt 8 bytes
  let (finraBestOfferSize, bytes) ← decodeUInt 4 bytes
  let (finraBestOfferMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBboLuldIndicator, bytes) ← FinraBboLuldIndicator.decode bytes
  let (highIndicationPrice, bytes) ← decodeUInt 8 bytes
  let (lowIndicationPrice, bytes) ← decodeUInt 8 bytes
  let (haltReason, bytes) ← HaltReason.decode bytes
  pure ({ participantId, securitySymbol, finraBestBidQuoteCondition, finraBestBidPrice, finraBestBidSize, finraBestBidMarketMakerId, finraBestOfferQuoteCondition, finraBestOfferPrice, finraBestOfferSize, finraBestOfferMarketMakerId, finraBboLuldIndicator, highIndicationPrice, lowIndicationPrice, haltReason }, bytes)

@[simp] theorem encode_length (message : FinraSnapshotMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Alpha.encode_length, encodeUInt_length, FinraBboLuldIndicator.encode_length, HaltReason.encode_length]

theorem encode_length_pos (message : FinraSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FinraSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinraBboLuldIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [HaltReason.decode_encode, some_bind]
  rfl

end FinraSnapshotMessage

/-- Any Snapshot Message Payload, selected by Snapshot Message Type -/
inductive SnapshotMessagePayload where
  | lineIntegrityMessage (message : LineIntegrityMessage) -- "T" 0x54
  | symbolReferenceDataMessage (message : SymbolReferenceDataMessage) -- "S" 0x53
  | marketWideCircuitBreakerDeclineLevelStatusSnapshotMessage (message : MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage) -- "K" 0x4B
  | consolidatedSnapshotMessage (message : ConsolidatedSnapshotMessage) -- "C" 0x43
  | participantSnapshotMessage (message : ParticipantSnapshotMessage) -- "P" 0x50
  | finraSnapshotMessage (message : FinraSnapshotMessage) -- "F" 0x46
  deriving DecidableEq, Repr

namespace SnapshotMessagePayload

/-- The Snapshot Message Type each message is sent under -/
def tag : SnapshotMessagePayload → BitVec 8
  | .lineIntegrityMessage _ => 84
  | .symbolReferenceDataMessage _ => 83
  | .marketWideCircuitBreakerDeclineLevelStatusSnapshotMessage _ => 75
  | .consolidatedSnapshotMessage _ => 67
  | .participantSnapshotMessage _ => 80
  | .finraSnapshotMessage _ => 70

def encode : SnapshotMessagePayload → List UInt8
  | .lineIntegrityMessage message => LineIntegrityMessage.encode message
  | .symbolReferenceDataMessage message => SymbolReferenceDataMessage.encode message
  | .marketWideCircuitBreakerDeclineLevelStatusSnapshotMessage message => MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage.encode message
  | .consolidatedSnapshotMessage message => ConsolidatedSnapshotMessage.encode message
  | .participantSnapshotMessage message => ParticipantSnapshotMessage.encode message
  | .finraSnapshotMessage message => FinraSnapshotMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SnapshotMessagePayload) : (encode message).length ≤ 96 := by
  cases message with
  | lineIntegrityMessage inner =>
    simp only [encode, LineIntegrityMessage.encode_length]
    omega
  | symbolReferenceDataMessage inner =>
    simp only [encode, SymbolReferenceDataMessage.encode_length]
    omega
  | marketWideCircuitBreakerDeclineLevelStatusSnapshotMessage inner =>
    simp only [encode, MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage.encode_length]
    omega
  | consolidatedSnapshotMessage inner =>
    simp only [encode, ConsolidatedSnapshotMessage.encode_length]
    omega
  | participantSnapshotMessage inner =>
    simp only [encode, ParticipantSnapshotMessage.encode_length]
    omega
  | finraSnapshotMessage inner =>
    simp only [encode, FinraSnapshotMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SnapshotMessagePayload × List UInt8) :=
  if tag = 84 then (LineIntegrityMessage.decode bytes).map fun (message, rest) => (.lineIntegrityMessage message, rest)
  else if tag = 83 then (SymbolReferenceDataMessage.decode bytes).map fun (message, rest) => (.symbolReferenceDataMessage message, rest)
  else if tag = 75 then (MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage.decode bytes).map fun (message, rest) => (.marketWideCircuitBreakerDeclineLevelStatusSnapshotMessage message, rest)
  else if tag = 67 then (ConsolidatedSnapshotMessage.decode bytes).map fun (message, rest) => (.consolidatedSnapshotMessage message, rest)
  else if tag = 80 then (ParticipantSnapshotMessage.decode bytes).map fun (message, rest) => (.participantSnapshotMessage message, rest)
  else if tag = 70 then (FinraSnapshotMessage.decode bytes).map fun (message, rest) => (.finraSnapshotMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SnapshotMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SnapshotMessagePayload

/-- Snapshot Message -/
structure SnapshotMessage where
  snapshotMessagePayload : SnapshotMessagePayload
  deriving DecidableEq, Repr

namespace SnapshotMessage

def encode (message : SnapshotMessage) : List UInt8 :=
  encodeUInt 1 (SnapshotMessagePayload.tag message.snapshotMessagePayload)
    ++ (SnapshotMessagePayload.encode message.snapshotMessagePayload)

def decode (bytes : List UInt8) : Option (SnapshotMessage × List UInt8) := do
  let (snapshotMessageType, bytes) ← decodeUInt 1 bytes
  let (snapshotMessagePayload, bytes) ← SnapshotMessagePayload.decode snapshotMessageType bytes
  pure ({ snapshotMessagePayload }, bytes)

theorem encode_length_pos (message : SnapshotMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotMessage) : (encode message).length ≤ 97 := by
  unfold encode
  cases message.snapshotMessagePayload with
  | lineIntegrityMessage inner =>
    simp only [SnapshotMessagePayload.encode, List.length_append, encodeUInt_length, LineIntegrityMessage.encode_length]
    omega
  | symbolReferenceDataMessage inner =>
    simp only [SnapshotMessagePayload.encode, List.length_append, encodeUInt_length, SymbolReferenceDataMessage.encode_length]
    omega
  | marketWideCircuitBreakerDeclineLevelStatusSnapshotMessage inner =>
    simp only [SnapshotMessagePayload.encode, List.length_append, encodeUInt_length, MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage.encode_length]
    omega
  | consolidatedSnapshotMessage inner =>
    simp only [SnapshotMessagePayload.encode, List.length_append, encodeUInt_length, ConsolidatedSnapshotMessage.encode_length]
    omega
  | participantSnapshotMessage inner =>
    simp only [SnapshotMessagePayload.encode, List.length_append, encodeUInt_length, ParticipantSnapshotMessage.encode_length]
    omega
  | finraSnapshotMessage inner =>
    simp only [SnapshotMessagePayload.encode, List.length_append, encodeUInt_length, FinraSnapshotMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SnapshotMessagePayload.decode_encode, some_bind]
  rfl

end SnapshotMessage

/-- Any Category Payload, selected by Message Category -/
inductive CategoryPayload where
  | snapshotMessage (message : SnapshotMessage) -- "R" 0x52
  deriving DecidableEq, Repr

namespace CategoryPayload

/-- The Message Category each message is sent under -/
def tag : CategoryPayload → BitVec 8
  | .snapshotMessage _ => 82

def encode : CategoryPayload → List UInt8
  | .snapshotMessage message => SnapshotMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : CategoryPayload) : (encode message).length ≤ 97 := by
  cases message with
  | snapshotMessage inner =>
    have bound_inner := SnapshotMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (CategoryPayload × List UInt8) :=
  if tag = 82 then (SnapshotMessage.decode bytes).map fun (message, rest) => (.snapshotMessage message, rest)
  else none

@[simp] theorem decode_encode (message : CategoryPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end CategoryPayload

/-- Message -/
structure Message where
  categoryPayload : CategoryPayload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (CategoryPayload.tag message.categoryPayload)
    ++ (CategoryPayload.encode message.categoryPayload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageCategory, bytes) ← decodeUInt 1 bytes
  let (categoryPayload, bytes) ← CategoryPayload.decode messageCategory bytes
  pure ({ categoryPayload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CategoryPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.categoryPayload with
  | snapshotMessage inner =>
    have bound_inner := SnapshotMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, encodeUInt_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  version : BitVec 8
  blockSize : BitVec 16
  blockSequenceNumber : BitVec 32
  deliveryflag : BitVec 8
  lastseqnum : BitVec 32
  totpubseqrollover : BitVec 8
  sipBlockTimestamp : SipBlockTimestamp
  blockChecksum : BitVec 16
  message : Bounded 1 Message
  blockPadByte : Capped 1
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.version
    ++ (encodeUInt 2 message.blockSize
    ++ (encodeUInt 4 message.blockSequenceNumber
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUInt 1 message.deliveryflag
    ++ (encodeUInt 4 message.lastseqnum
    ++ (encodeUInt 1 message.totpubseqrollover
    ++ (SipBlockTimestamp.encode message.sipBlockTimestamp
    ++ (encodeUInt 2 message.blockChecksum
    ++ (encodeMany Message.encode message.message.val
    ++ (message.blockPadByte.val))))))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (version, bytes) ← decodeUInt 1 bytes
  let (blockSize, bytes) ← decodeUInt 2 bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (messagesInBlock, bytes) ← decodeUInt 1 bytes
  let (deliveryflag, bytes) ← decodeUInt 1 bytes
  let (lastseqnum, bytes) ← decodeUInt 4 bytes
  let (totpubseqrollover, bytes) ← decodeUInt 1 bytes
  let (sipBlockTimestamp, bytes) ← SipBlockTimestamp.decode bytes
  let (blockChecksum, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messagesInBlock.toNat bytes
  let blockPadByte_ := bytes
  if fits_message : message_.length < 256 ^ 1 then
    if fits_blockPadByte : blockPadByte_.length ≤ 1 then
      pure { version, blockSize, blockSequenceNumber, deliveryflag, lastseqnum, totpubseqrollover, sipBlockTimestamp, blockChecksum, message := ⟨message_, fits_message⟩, blockPadByte := ⟨blockPadByte_, fits_blockPadByte⟩ }
    else none
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SipBlockTimestamp.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt, dite_eq_left message.blockPadByte.length_le]
  rfl

end Packet

end Omi.SiacCqsSnapshotCtaV21
