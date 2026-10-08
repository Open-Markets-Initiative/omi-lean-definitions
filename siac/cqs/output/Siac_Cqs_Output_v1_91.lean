import Wire

/-!
# The Securities Industry Automation Corporation Output v1.91

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.SiacCqsOutputCtaV191

/-- Retransmission Indicator: one byte code -/
def RetransmissionIndicator.codes : List UInt8 :=
  [0x4F, 0x56]

inductive RetransmissionIndicator where
  | original -- Original
  | retransmitted -- Retransmitted
  | unlisted (byte : { byte : UInt8 // byte ∉ RetransmissionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetransmissionIndicator

def toByte : RetransmissionIndicator → UInt8
  | .original => 0x4F
  | .retransmitted => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RetransmissionIndicator :=
  if byte = 0x4F then .original
  else .retransmitted

def ofByte (byte : UInt8) : RetransmissionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetransmissionIndicator) : ofByte value.toByte = value := by
  cases value with
  | original => decide
  | retransmitted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RetransmissionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetransmissionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RetransmissionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RetransmissionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RetransmissionIndicator

/-- Participant Id: one byte code -/
def ParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x53, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive ParticipantId where
  | nyseAmerican -- Nyse American
  | nasdaqBx -- Nasdaq Bx
  | nyseNational -- Nyse National
  | finraAdf -- Finra Adf
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseChicago -- Nyse Chicago
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | cqs -- Cqs
  | nasdaq -- Nasdaq
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqPsx -- Nasdaq Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | unlisted (byte : { byte : UInt8 // byte ∉ ParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ParticipantId

def toByte : ParticipantId → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqBx => 0x42
  | .nyseNational => 0x43
  | .finraAdf => 0x44
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseChicago => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .cqs => 0x53
  | .nasdaq => 0x54
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ParticipantId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finraAdf
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x53 then .cqs
  else if byte = 0x54 then .nasdaq
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqPsx
  else if byte = 0x59 then .cboeByx
  else .cboeBzx

def ofByte (byte : UInt8) : ParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ParticipantId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqBx => decide
  | nyseNational => decide
  | finraAdf => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseChicago => decide
  | nyse => decide
  | nyseArca => decide
  | cqs => decide
  | nasdaq => decide
  | iex => decide
  | cbsx => decide
  | nasdaqPsx => decide
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

/-- Market Wide Circuit Breaker Level Indicator: one byte code -/
def MarketWideCircuitBreakerLevelIndicator.codes : List UInt8 :=
  [0x20, 0x31, 0x32, 0x33]

inductive MarketWideCircuitBreakerLevelIndicator where
  | mwcbNotApplicable -- Mwcb Not Applicable
  | level1Breached -- Level 1 Breached
  | level2Breached -- Level 2 Breached
  | level3Breached -- Level 3 Breached
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketWideCircuitBreakerLevelIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerLevelIndicator

def toByte : MarketWideCircuitBreakerLevelIndicator → UInt8
  | .mwcbNotApplicable => 0x20
  | .level1Breached => 0x31
  | .level2Breached => 0x32
  | .level3Breached => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketWideCircuitBreakerLevelIndicator :=
  if byte = 0x20 then .mwcbNotApplicable
  else if byte = 0x31 then .level1Breached
  else if byte = 0x32 then .level2Breached
  else .level3Breached

def ofByte (byte : UInt8) : MarketWideCircuitBreakerLevelIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketWideCircuitBreakerLevelIndicator) : ofByte value.toByte = value := by
  cases value with
  | mwcbNotApplicable => decide
  | level1Breached => decide
  | level2Breached => decide
  | level3Breached => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketWideCircuitBreakerLevelIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketWideCircuitBreakerLevelIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketWideCircuitBreakerLevelIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketWideCircuitBreakerLevelIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketWideCircuitBreakerLevelIndicator

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

/-- Short Sale Restriction Indicator: one byte code -/
def ShortSaleRestrictionIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x43, 0x44, 0x45]

inductive ShortSaleRestrictionIndicator where
  | notInEffect -- Not In Effect
  | shortSaleRestrictionActivated -- Short Sale Restriction Activated
  | shortSaleRestrictionContinued -- Short Sale Restriction Continued
  | shortSaleRestrictionDeactivated -- Short Sale Restriction Deactivated
  | shortSaleRestrictionInEffect -- Short Sale Restriction In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSaleRestrictionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSaleRestrictionIndicator

def toByte : ShortSaleRestrictionIndicator → UInt8
  | .notInEffect => 0x20
  | .shortSaleRestrictionActivated => 0x41
  | .shortSaleRestrictionContinued => 0x43
  | .shortSaleRestrictionDeactivated => 0x44
  | .shortSaleRestrictionInEffect => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSaleRestrictionIndicator :=
  if byte = 0x20 then .notInEffect
  else if byte = 0x41 then .shortSaleRestrictionActivated
  else if byte = 0x43 then .shortSaleRestrictionContinued
  else if byte = 0x44 then .shortSaleRestrictionDeactivated
  else .shortSaleRestrictionInEffect

def ofByte (byte : UInt8) : ShortSaleRestrictionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSaleRestrictionIndicator) : ofByte value.toByte = value := by
  cases value with
  | notInEffect => decide
  | shortSaleRestrictionActivated => decide
  | shortSaleRestrictionContinued => decide
  | shortSaleRestrictionDeactivated => decide
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

/-- Primary Listing Market Participant Id: one byte code -/
def PrimaryListingMarketParticipantId.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x49, 0x4A, 0x4B, 0x4D, 0x4E, 0x50, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive PrimaryListingMarketParticipantId where
  | primaryListingMarketParticipantIdNotApplicable -- Primary Listing Market Participant Id Not Applicable
  | nyseAmerican -- Nyse American
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nyseNational -- Nyse National
  | finraAdf -- Finra Adf
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | nyseChicago -- Nyse Chicago
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
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
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .nyseChicago => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x54
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
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x54 then .nasdaq
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
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | nyseChicago => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
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
  | closedMarketMaker -- Closed Market Maker
  | nonFirmQuote -- Non Firm Quote
  | openingQuote -- Opening Quote
  | regularFinraOpen -- Regular Finra Open
  | slowQuoteDueToLiquidityReplenishmentPointOrGapQuoteOnBothTheBidAndOfferSides -- Slow Quote Due To Liquidity Replenishment Point Or Gap Quote On Both The Bid And Offer Sides
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
  | .closedMarketMaker => 0x4C
  | .nonFirmQuote => 0x4E
  | .openingQuote => 0x4F
  | .regularFinraOpen => 0x52
  | .slowQuoteDueToLiquidityReplenishmentPointOrGapQuoteOnBothTheBidAndOfferSides => 0x55
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
  else if byte = 0x4C then .closedMarketMaker
  else if byte = 0x4E then .nonFirmQuote
  else if byte = 0x4F then .openingQuote
  else if byte = 0x52 then .regularFinraOpen
  else if byte = 0x55 then .slowQuoteDueToLiquidityReplenishmentPointOrGapQuoteOnBothTheBidAndOfferSides
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
  | closedMarketMaker => decide
  | nonFirmQuote => decide
  | openingQuote => decide
  | regularFinraOpen => decide
  | slowQuoteDueToLiquidityReplenishmentPointOrGapQuoteOnBothTheBidAndOfferSides => decide
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

/-- Security Status Indicator: one byte code -/
def SecurityStatusIndicator.codes : List UInt8 :=
  [0x20, 0x44, 0x47, 0x49, 0x4D, 0x50, 0x54, 0x58, 0x59, 0x5A, 0x30, 0x31, 0x32, 0x33, 0x39]

inductive SecurityStatusIndicator where
  | notApplicable -- Not Applicable
  | newsDissemination -- News Dissemination
  | tradingRangeIndication -- Trading Range Indication
  | orderImbalance -- Order Imbalance
  | luldTradingPause -- Luld Trading Pause
  | newsPending -- News Pending
  | resume -- Resume
  | operational -- Operational
  | supPennyTrading -- Sup Penny Trading
  | noOpenNoResume -- No Open No Resume
  | luldPriceBand -- Luld Price Band
  | marketWideCircuitBreakerLevel1Breached -- Market Wide Circuit Breaker Level 1 Breached
  | marketWideCircuitBreakerLevel2Breached -- Market Wide Circuit Breaker Level 2 Breached
  | marketWideCircuitBreakerLevel3Breached -- Market Wide Circuit Breaker Level 3 Breached
  | republishedLuldPriceBand -- Republished Luld Price Band
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatusIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatusIndicator

def toByte : SecurityStatusIndicator → UInt8
  | .notApplicable => 0x20
  | .newsDissemination => 0x44
  | .tradingRangeIndication => 0x47
  | .orderImbalance => 0x49
  | .luldTradingPause => 0x4D
  | .newsPending => 0x50
  | .resume => 0x54
  | .operational => 0x58
  | .supPennyTrading => 0x59
  | .noOpenNoResume => 0x5A
  | .luldPriceBand => 0x30
  | .marketWideCircuitBreakerLevel1Breached => 0x31
  | .marketWideCircuitBreakerLevel2Breached => 0x32
  | .marketWideCircuitBreakerLevel3Breached => 0x33
  | .republishedLuldPriceBand => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatusIndicator :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x44 then .newsDissemination
  else if byte = 0x47 then .tradingRangeIndication
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x4D then .luldTradingPause
  else if byte = 0x50 then .newsPending
  else if byte = 0x54 then .resume
  else if byte = 0x58 then .operational
  else if byte = 0x59 then .supPennyTrading
  else if byte = 0x5A then .noOpenNoResume
  else if byte = 0x30 then .luldPriceBand
  else if byte = 0x31 then .marketWideCircuitBreakerLevel1Breached
  else if byte = 0x32 then .marketWideCircuitBreakerLevel2Breached
  else if byte = 0x33 then .marketWideCircuitBreakerLevel3Breached
  else .republishedLuldPriceBand

def ofByte (byte : UInt8) : SecurityStatusIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatusIndicator) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | newsDissemination => decide
  | tradingRangeIndication => decide
  | orderImbalance => decide
  | luldTradingPause => decide
  | newsPending => decide
  | resume => decide
  | operational => decide
  | supPennyTrading => decide
  | noOpenNoResume => decide
  | luldPriceBand => decide
  | marketWideCircuitBreakerLevel1Breached => decide
  | marketWideCircuitBreakerLevel2Breached => decide
  | marketWideCircuitBreakerLevel3Breached => decide
  | republishedLuldPriceBand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityStatusIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityStatusIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityStatusIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityStatusIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityStatusIndicator

/-- Retail Interest Indicator: one byte code -/
def RetailInterestIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43]

inductive RetailInterestIndicator where
  | notApplicable -- Not Applicable
  | retailInterestOnBidQuote -- Retail Interest On Bid Quote
  | retailInterestOnOfferQuote -- Retail Interest On Offer Quote
  | retailInterestOnBothTheBidAndOfferQuotes -- Retail Interest On Both The Bid And Offer Quotes
  | unlisted (byte : { byte : UInt8 // byte ∉ RetailInterestIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetailInterestIndicator

def toByte : RetailInterestIndicator → UInt8
  | .notApplicable => 0x20
  | .retailInterestOnBidQuote => 0x41
  | .retailInterestOnOfferQuote => 0x42
  | .retailInterestOnBothTheBidAndOfferQuotes => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RetailInterestIndicator :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x41 then .retailInterestOnBidQuote
  else if byte = 0x42 then .retailInterestOnOfferQuote
  else .retailInterestOnBothTheBidAndOfferQuotes

def ofByte (byte : UInt8) : RetailInterestIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetailInterestIndicator) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
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

/-- Finra Bbo Indicator: one byte code -/
def FinraBboIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42]

inductive FinraBboIndicator where
  | notApplicable -- Not Applicable
  | noFinraBboChange -- No Finra Bbo Change
  | noFinraBboExists -- No Finra Bbo Exists
  | unlisted (byte : { byte : UInt8 // byte ∉ FinraBboIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinraBboIndicator

def toByte : FinraBboIndicator → UInt8
  | .notApplicable => 0x20
  | .noFinraBboChange => 0x41
  | .noFinraBboExists => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinraBboIndicator :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x41 then .noFinraBboChange
  else .noFinraBboExists

def ofByte (byte : UInt8) : FinraBboIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinraBboIndicator) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | noFinraBboChange => decide
  | noFinraBboExists => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FinraBboIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinraBboIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FinraBboIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FinraBboIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FinraBboIndicator

/-- Sip Generated Message Identifier: one byte code -/
def SipGeneratedMessageIdentifier.codes : List UInt8 :=
  [0x20, 0x53]

inductive SipGeneratedMessageIdentifier where
  | notApplicable -- Not Applicable
  | consolidatedQuotationSystem -- Consolidated Quotation System
  | unlisted (byte : { byte : UInt8 // byte ∉ SipGeneratedMessageIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SipGeneratedMessageIdentifier

def toByte : SipGeneratedMessageIdentifier → UInt8
  | .notApplicable => 0x20
  | .consolidatedQuotationSystem => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SipGeneratedMessageIdentifier :=
  if byte = 0x20 then .notApplicable
  else .consolidatedQuotationSystem

def ofByte (byte : UInt8) : SipGeneratedMessageIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SipGeneratedMessageIdentifier) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | consolidatedQuotationSystem => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SipGeneratedMessageIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SipGeneratedMessageIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SipGeneratedMessageIdentifier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SipGeneratedMessageIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SipGeneratedMessageIdentifier

/-- National Bbo Luld Indicator: one byte code -/
def NationalBboLuldIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49]

inductive NationalBboLuldIndicator where
  | notApplicable -- Not Applicable
  | nationalBestBidAndOrNationalBestOfferAreExecutable -- National Best Bid And Or National Best Offer Are Executable
  | nationalBestBidBelowLowerLimitPriceBandAndIsNonExecutable -- National Best Bid Below Lower Limit Price Band And Is Non Executable
  | nationalBestOfferAboveUpperLimitPriceBandAndIsNonExecutable -- National Best Offer Above Upper Limit Price Band And Is Non Executable
  | nationalBestBidBelowLowerLimitPriceBandAndNationalBestOfferAboveUpperLimitPriceBandBothAreNonExecutable -- National Best Bid Below Lower Limit Price Band And National Best Offer Above Upper Limit Price Band Both Are Non Executable
  | nationalBestBidEqualsUpperLimitPriceBandAndIsInLimitState -- National Best Bid Equals Upper Limit Price Band And Is In Limit State
  | nationalBestOfferEqualsLowerLimitPriceBandAndIsInLimitState -- National Best Offer Equals Lower Limit Price Band And Is In Limit State
  | nationalBestBidEqualsUpperLimitPriceBandAndIsInLimitStateAndNationalBestOfferAboveUpperLimitPriceBandAndIsNonExecutable -- National Best Bid Equals Upper Limit Price Band And Is In Limit State And National Best Offer Above Upper Limit Price Band And Is Non Executable
  | nationalBestBidBelowLowerLimitPriceBandAndIsNonExecutableAndNationalBestOfferEqualsLowerLimitPriceBandAndIsInLimitState -- National Best Bid Below Lower Limit Price Band And Is Non Executable And National Best Offer Equals Lower Limit Price Band And Is In Limit State
  | nationalBestBidEqualsUpperLimitPriceBandAndNationalBestOfferEqualsLowerLimitPriceBand -- National Best Bid Equals Upper Limit Price Band And National Best Offer Equals Lower Limit Price Band
  | unlisted (byte : { byte : UInt8 // byte ∉ NationalBboLuldIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NationalBboLuldIndicator

def toByte : NationalBboLuldIndicator → UInt8
  | .notApplicable => 0x20
  | .nationalBestBidAndOrNationalBestOfferAreExecutable => 0x41
  | .nationalBestBidBelowLowerLimitPriceBandAndIsNonExecutable => 0x42
  | .nationalBestOfferAboveUpperLimitPriceBandAndIsNonExecutable => 0x43
  | .nationalBestBidBelowLowerLimitPriceBandAndNationalBestOfferAboveUpperLimitPriceBandBothAreNonExecutable => 0x44
  | .nationalBestBidEqualsUpperLimitPriceBandAndIsInLimitState => 0x45
  | .nationalBestOfferEqualsLowerLimitPriceBandAndIsInLimitState => 0x46
  | .nationalBestBidEqualsUpperLimitPriceBandAndIsInLimitStateAndNationalBestOfferAboveUpperLimitPriceBandAndIsNonExecutable => 0x47
  | .nationalBestBidBelowLowerLimitPriceBandAndIsNonExecutableAndNationalBestOfferEqualsLowerLimitPriceBandAndIsInLimitState => 0x48
  | .nationalBestBidEqualsUpperLimitPriceBandAndNationalBestOfferEqualsLowerLimitPriceBand => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NationalBboLuldIndicator :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x41 then .nationalBestBidAndOrNationalBestOfferAreExecutable
  else if byte = 0x42 then .nationalBestBidBelowLowerLimitPriceBandAndIsNonExecutable
  else if byte = 0x43 then .nationalBestOfferAboveUpperLimitPriceBandAndIsNonExecutable
  else if byte = 0x44 then .nationalBestBidBelowLowerLimitPriceBandAndNationalBestOfferAboveUpperLimitPriceBandBothAreNonExecutable
  else if byte = 0x45 then .nationalBestBidEqualsUpperLimitPriceBandAndIsInLimitState
  else if byte = 0x46 then .nationalBestOfferEqualsLowerLimitPriceBandAndIsInLimitState
  else if byte = 0x47 then .nationalBestBidEqualsUpperLimitPriceBandAndIsInLimitStateAndNationalBestOfferAboveUpperLimitPriceBandAndIsNonExecutable
  else if byte = 0x48 then .nationalBestBidBelowLowerLimitPriceBandAndIsNonExecutableAndNationalBestOfferEqualsLowerLimitPriceBandAndIsInLimitState
  else .nationalBestBidEqualsUpperLimitPriceBandAndNationalBestOfferEqualsLowerLimitPriceBand

def ofByte (byte : UInt8) : NationalBboLuldIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NationalBboLuldIndicator) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | nationalBestBidAndOrNationalBestOfferAreExecutable => decide
  | nationalBestBidBelowLowerLimitPriceBandAndIsNonExecutable => decide
  | nationalBestOfferAboveUpperLimitPriceBandAndIsNonExecutable => decide
  | nationalBestBidBelowLowerLimitPriceBandAndNationalBestOfferAboveUpperLimitPriceBandBothAreNonExecutable => decide
  | nationalBestBidEqualsUpperLimitPriceBandAndIsInLimitState => decide
  | nationalBestOfferEqualsLowerLimitPriceBandAndIsInLimitState => decide
  | nationalBestBidEqualsUpperLimitPriceBandAndIsInLimitStateAndNationalBestOfferAboveUpperLimitPriceBandAndIsNonExecutable => decide
  | nationalBestBidBelowLowerLimitPriceBandAndIsNonExecutableAndNationalBestOfferEqualsLowerLimitPriceBandAndIsInLimitState => decide
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

/-- Best Bid Participant Id: one byte code -/
def BestBidParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x53, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive BestBidParticipantId where
  | nyseAmerican -- Nyse American
  | nasdaqBx -- Nasdaq Bx
  | nyseNational -- Nyse National
  | finraAdf -- Finra Adf
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseChicago -- Nyse Chicago
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | cqs -- Cqs
  | nasdaq -- Nasdaq
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqPsx -- Nasdaq Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | unlisted (byte : { byte : UInt8 // byte ∉ BestBidParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BestBidParticipantId

def toByte : BestBidParticipantId → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqBx => 0x42
  | .nyseNational => 0x43
  | .finraAdf => 0x44
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseChicago => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .cqs => 0x53
  | .nasdaq => 0x54
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BestBidParticipantId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finraAdf
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x53 then .cqs
  else if byte = 0x54 then .nasdaq
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqPsx
  else if byte = 0x59 then .cboeByx
  else .cboeBzx

def ofByte (byte : UInt8) : BestBidParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BestBidParticipantId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqBx => decide
  | nyseNational => decide
  | finraAdf => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseChicago => decide
  | nyse => decide
  | nyseArca => decide
  | cqs => decide
  | nasdaq => decide
  | iex => decide
  | cbsx => decide
  | nasdaqPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BestBidParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BestBidParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BestBidParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BestBidParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BestBidParticipantId

/-- Best Offer Participant Id: one byte code -/
def BestOfferParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x53, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive BestOfferParticipantId where
  | nyseAmerican -- Nyse American
  | nasdaqBx -- Nasdaq Bx
  | nyseNational -- Nyse National
  | finraAdf -- Finra Adf
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseChicago -- Nyse Chicago
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | cqs -- Cqs
  | nasdaq -- Nasdaq
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqPsx -- Nasdaq Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | unlisted (byte : { byte : UInt8 // byte ∉ BestOfferParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BestOfferParticipantId

def toByte : BestOfferParticipantId → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqBx => 0x42
  | .nyseNational => 0x43
  | .finraAdf => 0x44
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseChicago => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .cqs => 0x53
  | .nasdaq => 0x54
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BestOfferParticipantId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finraAdf
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x53 then .cqs
  else if byte = 0x54 then .nasdaq
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqPsx
  else if byte = 0x59 then .cboeByx
  else .cboeBzx

def ofByte (byte : UInt8) : BestOfferParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BestOfferParticipantId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqBx => decide
  | nyseNational => decide
  | finraAdf => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseChicago => decide
  | nyse => decide
  | nyseArca => decide
  | cqs => decide
  | nasdaq => decide
  | iex => decide
  | cbsx => decide
  | nasdaqPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BestOfferParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BestOfferParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BestOfferParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BestOfferParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BestOfferParticipantId

/-- Finra Bbo Luld Indicator: one byte code -/
def FinraBboLuldIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44]

inductive FinraBboLuldIndicator where
  | limitUpLimitDownNotApplicable -- Limit Up Limit Down Not Applicable
  | finraBestBidAndOrFinraBestOfferAreExecutable -- Finra Best Bid And Or Finra Best Offer Are Executable
  | finraBestBidBelowLowerLimitPriceBandAndFinraBestBidIsNonExecutable -- Finra Best Bid Below Lower Limit Price Band And Finra Best Bid Is Non Executable
  | finraBestOfferAboveUpperLimitPriceBandAndFinraBestOfferIsNonExecutable -- Finra Best Offer Above Upper Limit Price Band And Finra Best Offer Is Non Executable
  | bestBidBelowLowerLimitPriceBandAndBestOfferAboveUpperLimitPriceBandBestBidAndBestOfferAreNonExecutableForFinra -- Best Bid Below Lower Limit Price Band And Best Offer Above Upper Limit Price Band Best Bid And Best Offer Are Non Executable For Finra
  | unlisted (byte : { byte : UInt8 // byte ∉ FinraBboLuldIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinraBboLuldIndicator

def toByte : FinraBboLuldIndicator → UInt8
  | .limitUpLimitDownNotApplicable => 0x20
  | .finraBestBidAndOrFinraBestOfferAreExecutable => 0x41
  | .finraBestBidBelowLowerLimitPriceBandAndFinraBestBidIsNonExecutable => 0x42
  | .finraBestOfferAboveUpperLimitPriceBandAndFinraBestOfferIsNonExecutable => 0x43
  | .bestBidBelowLowerLimitPriceBandAndBestOfferAboveUpperLimitPriceBandBestBidAndBestOfferAreNonExecutableForFinra => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinraBboLuldIndicator :=
  if byte = 0x20 then .limitUpLimitDownNotApplicable
  else if byte = 0x41 then .finraBestBidAndOrFinraBestOfferAreExecutable
  else if byte = 0x42 then .finraBestBidBelowLowerLimitPriceBandAndFinraBestBidIsNonExecutable
  else if byte = 0x43 then .finraBestOfferAboveUpperLimitPriceBandAndFinraBestOfferIsNonExecutable
  else .bestBidBelowLowerLimitPriceBandAndBestOfferAboveUpperLimitPriceBandBestBidAndBestOfferAreNonExecutableForFinra

def ofByte (byte : UInt8) : FinraBboLuldIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinraBboLuldIndicator) : ofByte value.toByte = value := by
  cases value with
  | limitUpLimitDownNotApplicable => decide
  | finraBestBidAndOrFinraBestOfferAreExecutable => decide
  | finraBestBidBelowLowerLimitPriceBandAndFinraBestBidIsNonExecutable => decide
  | finraBestOfferAboveUpperLimitPriceBandAndFinraBestOfferIsNonExecutable => decide
  | bestBidBelowLowerLimitPriceBandAndBestOfferAboveUpperLimitPriceBandBestBidAndBestOfferAreNonExecutableForFinra => decide
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

/-- Participant Timestamp: 8 bytes -/
structure ParticipantTimestamp where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace ParticipantTimestamp

def encode (message : ParticipantTimestamp) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (ParticipantTimestamp × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : ParticipantTimestamp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ParticipantTimestamp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ParticipantTimestamp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ParticipantTimestamp

/-- Administrative Unformatted Message: 26 bytes -/
structure AdministrativeUnformattedMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  text : Alpha 4
  deriving DecidableEq, Repr

namespace AdministrativeUnformattedMessage

def encode (message : AdministrativeUnformattedMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.text)))))

def decode (bytes : List UInt8) : Option (AdministrativeUnformattedMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (text, bytes) ← Alpha.decode 4 bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber, text }, bytes)

@[simp] theorem encode_length (message : AdministrativeUnformattedMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : AdministrativeUnformattedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdministrativeUnformattedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AdministrativeUnformattedMessage

/-- Any Administrative Message Payload, selected by Administrative Message Type -/
inductive AdministrativeMessagePayload where
  | administrativeUnformattedMessage (message : AdministrativeUnformattedMessage) -- "H" 0x48
  deriving DecidableEq, Repr

namespace AdministrativeMessagePayload

/-- The Administrative Message Type each message is sent under -/
def tag : AdministrativeMessagePayload → BitVec 8
  | .administrativeUnformattedMessage _ => 72

def encode : AdministrativeMessagePayload → List UInt8
  | .administrativeUnformattedMessage message => AdministrativeUnformattedMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AdministrativeMessagePayload) : (encode message).length ≤ 26 := by
  cases message with
  | administrativeUnformattedMessage inner =>
    simp only [encode, AdministrativeUnformattedMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AdministrativeMessagePayload × List UInt8) :=
  if tag = 72 then (AdministrativeUnformattedMessage.decode bytes).map fun (message, rest) => (.administrativeUnformattedMessage message, rest)
  else none

@[simp] theorem decode_encode (message : AdministrativeMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end AdministrativeMessagePayload

/-- Administrative Message -/
structure AdministrativeMessage where
  administrativeMessagePayload : AdministrativeMessagePayload
  deriving DecidableEq, Repr

namespace AdministrativeMessage

def encode (message : AdministrativeMessage) : List UInt8 :=
  encodeUInt 1 (AdministrativeMessagePayload.tag message.administrativeMessagePayload)
    ++ (AdministrativeMessagePayload.encode message.administrativeMessagePayload)

def decode (bytes : List UInt8) : Option (AdministrativeMessage × List UInt8) := do
  let (administrativeMessageType, bytes) ← decodeUInt 1 bytes
  let (administrativeMessagePayload, bytes) ← AdministrativeMessagePayload.decode administrativeMessageType bytes
  pure ({ administrativeMessagePayload }, bytes)

theorem encode_length_pos (message : AdministrativeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AdministrativeMessage) : (encode message).length ≤ 27 := by
  unfold encode
  cases message.administrativeMessagePayload with
  | administrativeUnformattedMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, AdministrativeUnformattedMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : AdministrativeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [AdministrativeMessagePayload.decode_encode, some_bind]
  rfl

end AdministrativeMessage

/-- Start Of Day Message: 22 bytes -/
structure StartOfDayMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StartOfDayMessage

def encode (message : StartOfDayMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (StartOfDayMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : StartOfDayMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StartOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfDayMessage

/-- Finra Close Message: 22 bytes -/
structure FinraCloseMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace FinraCloseMessage

def encode (message : FinraCloseMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (FinraCloseMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : FinraCloseMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FinraCloseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FinraCloseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FinraCloseMessage

/-- Reset Block Sequence Number Message: 22 bytes -/
structure ResetBlockSequenceNumberMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace ResetBlockSequenceNumberMessage

def encode (message : ResetBlockSequenceNumberMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (ResetBlockSequenceNumberMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : ResetBlockSequenceNumberMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ResetBlockSequenceNumberMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResetBlockSequenceNumberMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ResetBlockSequenceNumberMessage

/-- Start Of Test Cycle Message: 22 bytes -/
structure StartOfTestCycleMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StartOfTestCycleMessage

def encode (message : StartOfTestCycleMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (StartOfTestCycleMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : StartOfTestCycleMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StartOfTestCycleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfTestCycleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfTestCycleMessage

/-- End Of Test Cycle Message: 22 bytes -/
structure EndOfTestCycleMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace EndOfTestCycleMessage

def encode (message : EndOfTestCycleMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (EndOfTestCycleMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : EndOfTestCycleMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length]

theorem encode_length_pos (message : EndOfTestCycleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTestCycleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndOfTestCycleMessage

/-- Finra Open Message: 22 bytes -/
structure FinraOpenMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace FinraOpenMessage

def encode (message : FinraOpenMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (FinraOpenMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : FinraOpenMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FinraOpenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FinraOpenMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FinraOpenMessage

/-- Disaster Recovery Data Center Activation Message: 22 bytes -/
structure DisasterRecoveryDataCenterActivationMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace DisasterRecoveryDataCenterActivationMessage

def encode (message : DisasterRecoveryDataCenterActivationMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (DisasterRecoveryDataCenterActivationMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : DisasterRecoveryDataCenterActivationMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DisasterRecoveryDataCenterActivationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisasterRecoveryDataCenterActivationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DisasterRecoveryDataCenterActivationMessage

/-- Line Integrity Message: 22 bytes -/
structure LineIntegrityMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LineIntegrityMessage

def encode (message : LineIntegrityMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (LineIntegrityMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : LineIntegrityMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LineIntegrityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LineIntegrityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LineIntegrityMessage

/-- End Of Day Message: 22 bytes -/
structure EndOfDayMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace EndOfDayMessage

def encode (message : EndOfDayMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (EndOfDayMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : EndOfDayMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length]

theorem encode_length_pos (message : EndOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndOfDayMessage

/-- Any Control Message Payload, selected by Control Message Type -/
inductive ControlMessagePayload where
  | startOfDayMessage (message : StartOfDayMessage) -- "A" 0x41
  | finraCloseMessage (message : FinraCloseMessage) -- "C" 0x43
  | resetBlockSequenceNumberMessage (message : ResetBlockSequenceNumberMessage) -- "L" 0x4C
  | startOfTestCycleMessage (message : StartOfTestCycleMessage) -- "M" 0x4D
  | endOfTestCycleMessage (message : EndOfTestCycleMessage) -- "N" 0x4E
  | finraOpenMessage (message : FinraOpenMessage) -- "O" 0x4F
  | disasterRecoveryDataCenterActivationMessage (message : DisasterRecoveryDataCenterActivationMessage) -- "P" 0x50
  | lineIntegrityMessage (message : LineIntegrityMessage) -- "T" 0x54
  | endOfDayMessage (message : EndOfDayMessage) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace ControlMessagePayload

/-- The Control Message Type each message is sent under -/
def tag : ControlMessagePayload → BitVec 8
  | .startOfDayMessage _ => 65
  | .finraCloseMessage _ => 67
  | .resetBlockSequenceNumberMessage _ => 76
  | .startOfTestCycleMessage _ => 77
  | .endOfTestCycleMessage _ => 78
  | .finraOpenMessage _ => 79
  | .disasterRecoveryDataCenterActivationMessage _ => 80
  | .lineIntegrityMessage _ => 84
  | .endOfDayMessage _ => 90

def encode : ControlMessagePayload → List UInt8
  | .startOfDayMessage message => StartOfDayMessage.encode message
  | .finraCloseMessage message => FinraCloseMessage.encode message
  | .resetBlockSequenceNumberMessage message => ResetBlockSequenceNumberMessage.encode message
  | .startOfTestCycleMessage message => StartOfTestCycleMessage.encode message
  | .endOfTestCycleMessage message => EndOfTestCycleMessage.encode message
  | .finraOpenMessage message => FinraOpenMessage.encode message
  | .disasterRecoveryDataCenterActivationMessage message => DisasterRecoveryDataCenterActivationMessage.encode message
  | .lineIntegrityMessage message => LineIntegrityMessage.encode message
  | .endOfDayMessage message => EndOfDayMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ControlMessagePayload) : (encode message).length ≤ 22 := by
  cases message with
  | startOfDayMessage inner =>
    simp only [encode, StartOfDayMessage.encode_length]
    omega
  | finraCloseMessage inner =>
    simp only [encode, FinraCloseMessage.encode_length]
    omega
  | resetBlockSequenceNumberMessage inner =>
    simp only [encode, ResetBlockSequenceNumberMessage.encode_length]
    omega
  | startOfTestCycleMessage inner =>
    simp only [encode, StartOfTestCycleMessage.encode_length]
    omega
  | endOfTestCycleMessage inner =>
    simp only [encode, EndOfTestCycleMessage.encode_length]
    omega
  | finraOpenMessage inner =>
    simp only [encode, FinraOpenMessage.encode_length]
    omega
  | disasterRecoveryDataCenterActivationMessage inner =>
    simp only [encode, DisasterRecoveryDataCenterActivationMessage.encode_length]
    omega
  | lineIntegrityMessage inner =>
    simp only [encode, LineIntegrityMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [encode, EndOfDayMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ControlMessagePayload × List UInt8) :=
  if tag = 65 then (StartOfDayMessage.decode bytes).map fun (message, rest) => (.startOfDayMessage message, rest)
  else if tag = 67 then (FinraCloseMessage.decode bytes).map fun (message, rest) => (.finraCloseMessage message, rest)
  else if tag = 76 then (ResetBlockSequenceNumberMessage.decode bytes).map fun (message, rest) => (.resetBlockSequenceNumberMessage message, rest)
  else if tag = 77 then (StartOfTestCycleMessage.decode bytes).map fun (message, rest) => (.startOfTestCycleMessage message, rest)
  else if tag = 78 then (EndOfTestCycleMessage.decode bytes).map fun (message, rest) => (.endOfTestCycleMessage message, rest)
  else if tag = 79 then (FinraOpenMessage.decode bytes).map fun (message, rest) => (.finraOpenMessage message, rest)
  else if tag = 80 then (DisasterRecoveryDataCenterActivationMessage.decode bytes).map fun (message, rest) => (.disasterRecoveryDataCenterActivationMessage message, rest)
  else if tag = 84 then (LineIntegrityMessage.decode bytes).map fun (message, rest) => (.lineIntegrityMessage message, rest)
  else if tag = 90 then (EndOfDayMessage.decode bytes).map fun (message, rest) => (.endOfDayMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ControlMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ControlMessagePayload

/-- Control Message -/
structure ControlMessage where
  controlMessagePayload : ControlMessagePayload
  deriving DecidableEq, Repr

namespace ControlMessage

def encode (message : ControlMessage) : List UInt8 :=
  encodeUInt 1 (ControlMessagePayload.tag message.controlMessagePayload)
    ++ (ControlMessagePayload.encode message.controlMessagePayload)

def decode (bytes : List UInt8) : Option (ControlMessage × List UInt8) := do
  let (controlMessageType, bytes) ← decodeUInt 1 bytes
  let (controlMessagePayload, bytes) ← ControlMessagePayload.decode controlMessageType bytes
  pure ({ controlMessagePayload }, bytes)

theorem encode_length_pos (message : ControlMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ControlMessage) : (encode message).length ≤ 23 := by
  unfold encode
  cases message.controlMessagePayload with
  | startOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, StartOfDayMessage.encode_length]
    omega
  | finraCloseMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, FinraCloseMessage.encode_length]
    omega
  | resetBlockSequenceNumberMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, ResetBlockSequenceNumberMessage.encode_length]
    omega
  | startOfTestCycleMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, StartOfTestCycleMessage.encode_length]
    omega
  | endOfTestCycleMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, EndOfTestCycleMessage.encode_length]
    omega
  | finraOpenMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, FinraOpenMessage.encode_length]
    omega
  | disasterRecoveryDataCenterActivationMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, DisasterRecoveryDataCenterActivationMessage.encode_length]
    omega
  | lineIntegrityMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, LineIntegrityMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, EndOfDayMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ControlMessagePayload.decode_encode, some_bind]
  rfl

end ControlMessage

/-- Market Wide Circuit Breaker Decline Level Status Message: 47 bytes -/
structure MarketWideCircuitBreakerDeclineLevelStatusMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  mwcbLevel1 : BitVec 64
  mwcbLevel2 : BitVec 64
  mwcbLevel3 : BitVec 64
  reserved : BitVec 8
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerDeclineLevelStatusMessage

def encode (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (encodeUInt 8 message.mwcbLevel1
    ++ (encodeUInt 8 message.mwcbLevel2
    ++ (encodeUInt 8 message.mwcbLevel3
    ++ (encodeUInt 1 message.reserved))))))))

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerDeclineLevelStatusMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel1, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel2, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel3, bytes) ← decodeUInt 8 bytes
  let (reserved, bytes) ← decodeUInt 1 bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber, mwcbLevel1, mwcbLevel2, mwcbLevel3, reserved }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketWideCircuitBreakerDeclineLevelStatusMessage

/-- Market Wide Circuit Breaker Status Message: 24 bytes -/
structure MarketWideCircuitBreakerStatusMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  marketWideCircuitBreakerLevelIndicator : MarketWideCircuitBreakerLevelIndicator
  reserved : BitVec 8
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerStatusMessage

def encode (message : MarketWideCircuitBreakerStatusMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (MarketWideCircuitBreakerLevelIndicator.encode message.marketWideCircuitBreakerLevelIndicator
    ++ (encodeUInt 1 message.reserved))))))

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerStatusMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (marketWideCircuitBreakerLevelIndicator, bytes) ← MarketWideCircuitBreakerLevelIndicator.decode bytes
  let (reserved, bytes) ← decodeUInt 1 bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber, marketWideCircuitBreakerLevelIndicator, reserved }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerStatusMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, MarketWideCircuitBreakerLevelIndicator.encode_length]

theorem encode_length_pos (message : MarketWideCircuitBreakerStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketWideCircuitBreakerStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MarketWideCircuitBreakerLevelIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketWideCircuitBreakerStatusMessage

/-- Any Market Status Message Payload, selected by Market Status Message Type -/
inductive MarketStatusMessagePayload where
  | marketWideCircuitBreakerDeclineLevelStatusMessage (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) -- "M" 0x4D
  | marketWideCircuitBreakerStatusMessage (message : MarketWideCircuitBreakerStatusMessage) -- "L" 0x4C
  deriving DecidableEq, Repr

namespace MarketStatusMessagePayload

/-- The Market Status Message Type each message is sent under -/
def tag : MarketStatusMessagePayload → BitVec 8
  | .marketWideCircuitBreakerDeclineLevelStatusMessage _ => 77
  | .marketWideCircuitBreakerStatusMessage _ => 76

def encode : MarketStatusMessagePayload → List UInt8
  | .marketWideCircuitBreakerDeclineLevelStatusMessage message => MarketWideCircuitBreakerDeclineLevelStatusMessage.encode message
  | .marketWideCircuitBreakerStatusMessage message => MarketWideCircuitBreakerStatusMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MarketStatusMessagePayload) : (encode message).length ≤ 47 := by
  cases message with
  | marketWideCircuitBreakerDeclineLevelStatusMessage inner =>
    simp only [encode, MarketWideCircuitBreakerDeclineLevelStatusMessage.encode_length]
    omega
  | marketWideCircuitBreakerStatusMessage inner =>
    simp only [encode, MarketWideCircuitBreakerStatusMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (MarketStatusMessagePayload × List UInt8) :=
  if tag = 77 then (MarketWideCircuitBreakerDeclineLevelStatusMessage.decode bytes).map fun (message, rest) => (.marketWideCircuitBreakerDeclineLevelStatusMessage message, rest)
  else if tag = 76 then (MarketWideCircuitBreakerStatusMessage.decode bytes).map fun (message, rest) => (.marketWideCircuitBreakerStatusMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MarketStatusMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MarketStatusMessagePayload

/-- Market Status Message -/
structure MarketStatusMessage where
  marketStatusMessagePayload : MarketStatusMessagePayload
  deriving DecidableEq, Repr

namespace MarketStatusMessage

def encode (message : MarketStatusMessage) : List UInt8 :=
  encodeUInt 1 (MarketStatusMessagePayload.tag message.marketStatusMessagePayload)
    ++ (MarketStatusMessagePayload.encode message.marketStatusMessagePayload)

def decode (bytes : List UInt8) : Option (MarketStatusMessage × List UInt8) := do
  let (marketStatusMessageType, bytes) ← decodeUInt 1 bytes
  let (marketStatusMessagePayload, bytes) ← MarketStatusMessagePayload.decode marketStatusMessageType bytes
  pure ({ marketStatusMessagePayload }, bytes)

theorem encode_length_pos (message : MarketStatusMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketStatusMessage) : (encode message).length ≤ 48 := by
  unfold encode
  cases message.marketStatusMessagePayload with
  | marketWideCircuitBreakerDeclineLevelStatusMessage inner =>
    simp only [MarketStatusMessagePayload.encode, List.length_append, encodeUInt_length, MarketWideCircuitBreakerDeclineLevelStatusMessage.encode_length]
    omega
  | marketWideCircuitBreakerStatusMessage inner =>
    simp only [MarketStatusMessagePayload.encode, List.length_append, encodeUInt_length, MarketWideCircuitBreakerStatusMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : MarketStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MarketStatusMessagePayload.decode_encode, some_bind]
  rfl

end MarketStatusMessage

/-- Auction Status Message: 63 bytes -/
structure AuctionStatusMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbolLong : Alpha 11
  instrumentType : InstrumentType
  auctionCollarReferencePrice : BitVec 64
  auctionCollarUpperThresholdPrice : BitVec 64
  auctionCollarLowerThresholdPrice : BitVec 64
  numberOfExtensions : BitVec 8
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  future : Alpha 1
  deriving DecidableEq, Repr

namespace AuctionStatusMessage

def encode (message : AuctionStatusMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbolLong
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUInt 8 message.auctionCollarReferencePrice
    ++ (encodeUInt 8 message.auctionCollarUpperThresholdPrice
    ++ (encodeUInt 8 message.auctionCollarLowerThresholdPrice
    ++ (encodeUInt 1 message.numberOfExtensions
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (Alpha.encode message.future))))))))))))))

def decode (bytes : List UInt8) : Option (AuctionStatusMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbolLong, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (auctionCollarReferencePrice, bytes) ← decodeUInt 8 bytes
  let (auctionCollarUpperThresholdPrice, bytes) ← decodeUInt 8 bytes
  let (auctionCollarLowerThresholdPrice, bytes) ← decodeUInt 8 bytes
  let (numberOfExtensions, bytes) ← decodeUInt 1 bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (future, bytes) ← Alpha.decode 1 bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber, securitySymbolLong, instrumentType, auctionCollarReferencePrice, auctionCollarUpperThresholdPrice, auctionCollarLowerThresholdPrice, numberOfExtensions, shortSaleRestrictionIndicator, primaryListingMarketParticipantId, financialStatusIndicator, future }, bytes)

@[simp] theorem encode_length (message : AuctionStatusMessage) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length]

theorem encode_length_pos (message : AuctionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AuctionStatusMessage

/-- Adf Timestamp: 8 bytes -/
structure AdfTimestamp where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace AdfTimestamp

def encode (message : AdfTimestamp) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (AdfTimestamp × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : AdfTimestamp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AdfTimestamp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdfTimestamp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AdfTimestamp

/-- National Best Bid Long Appendage: 18 bytes -/
structure NationalBestBidLongAppendage where
  bestBidParticipantId : BestBidParticipantId
  bestBidQuoteCondition : Alpha 1
  bestBidPriceLong : BitVec 64
  bestBidSizeLong : BitVec 32
  finraBestBidMarketMakerId : Alpha 4
  deriving DecidableEq, Repr

namespace NationalBestBidLongAppendage

def encode (message : NationalBestBidLongAppendage) : List UInt8 :=
  BestBidParticipantId.encode message.bestBidParticipantId
    ++ (Alpha.encode message.bestBidQuoteCondition
    ++ (encodeUInt 8 message.bestBidPriceLong
    ++ (encodeUInt 4 message.bestBidSizeLong
    ++ (Alpha.encode message.finraBestBidMarketMakerId))))

def decode (bytes : List UInt8) : Option (NationalBestBidLongAppendage × List UInt8) := do
  let (bestBidParticipantId, bytes) ← BestBidParticipantId.decode bytes
  let (bestBidQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (bestBidPriceLong, bytes) ← decodeUInt 8 bytes
  let (bestBidSizeLong, bytes) ← decodeUInt 4 bytes
  let (finraBestBidMarketMakerId, bytes) ← Alpha.decode 4 bytes
  pure ({ bestBidParticipantId, bestBidQuoteCondition, bestBidPriceLong, bestBidSizeLong, finraBestBidMarketMakerId }, bytes)

@[simp] theorem encode_length (message : NationalBestBidLongAppendage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, BestBidParticipantId.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NationalBestBidLongAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NationalBestBidLongAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, BestBidParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NationalBestBidLongAppendage

/-- National Best Offer Long Appendage: 18 bytes -/
structure NationalBestOfferLongAppendage where
  bestOfferParticipantId : BestOfferParticipantId
  bestOfferQuoteCondition : Alpha 1
  bestOfferPriceLong : BitVec 64
  bestOfferSizeLong : BitVec 32
  finraBestOfferMarketMakerId : Alpha 4
  deriving DecidableEq, Repr

namespace NationalBestOfferLongAppendage

def encode (message : NationalBestOfferLongAppendage) : List UInt8 :=
  BestOfferParticipantId.encode message.bestOfferParticipantId
    ++ (Alpha.encode message.bestOfferQuoteCondition
    ++ (encodeUInt 8 message.bestOfferPriceLong
    ++ (encodeUInt 4 message.bestOfferSizeLong
    ++ (Alpha.encode message.finraBestOfferMarketMakerId))))

def decode (bytes : List UInt8) : Option (NationalBestOfferLongAppendage × List UInt8) := do
  let (bestOfferParticipantId, bytes) ← BestOfferParticipantId.decode bytes
  let (bestOfferQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (bestOfferPriceLong, bytes) ← decodeUInt 8 bytes
  let (bestOfferSizeLong, bytes) ← decodeUInt 4 bytes
  let (finraBestOfferMarketMakerId, bytes) ← Alpha.decode 4 bytes
  pure ({ bestOfferParticipantId, bestOfferQuoteCondition, bestOfferPriceLong, bestOfferSizeLong, finraBestOfferMarketMakerId }, bytes)

@[simp] theorem encode_length (message : NationalBestOfferLongAppendage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, BestOfferParticipantId.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NationalBestOfferLongAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NationalBestOfferLongAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, BestOfferParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NationalBestOfferLongAppendage

/-- National Best Bid Long Appendage: 36 bytes -/
structure NationalBestBidLongAppendageNationalBestOfferLongAppendage where
  nationalBestBidLongAppendage : NationalBestBidLongAppendage
  nationalBestOfferLongAppendage : NationalBestOfferLongAppendage
  deriving DecidableEq, Repr

namespace NationalBestBidLongAppendageNationalBestOfferLongAppendage

def encode (message : NationalBestBidLongAppendageNationalBestOfferLongAppendage) : List UInt8 :=
  NationalBestBidLongAppendage.encode message.nationalBestBidLongAppendage
    ++ (NationalBestOfferLongAppendage.encode message.nationalBestOfferLongAppendage)

def decode (bytes : List UInt8) : Option (NationalBestBidLongAppendageNationalBestOfferLongAppendage × List UInt8) := do
  let (nationalBestBidLongAppendage, bytes) ← NationalBestBidLongAppendage.decode bytes
  let (nationalBestOfferLongAppendage, bytes) ← NationalBestOfferLongAppendage.decode bytes
  pure ({ nationalBestBidLongAppendage, nationalBestOfferLongAppendage }, bytes)

@[simp] theorem encode_length (message : NationalBestBidLongAppendageNationalBestOfferLongAppendage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, NationalBestBidLongAppendage.encode_length, NationalBestOfferLongAppendage.encode_length]

theorem encode_length_pos (message : NationalBestBidLongAppendageNationalBestOfferLongAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NationalBestBidLongAppendageNationalBestOfferLongAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, NationalBestBidLongAppendage.decode_encode, some_bind]
  dsimp only
  rw [NationalBestOfferLongAppendage.decode_encode, some_bind]
  rfl

end NationalBestBidLongAppendageNationalBestOfferLongAppendage

/-- National Best Bid Short Appendage: 5 bytes -/
structure NationalBestBidShortAppendage where
  bestBidParticipantId : BestBidParticipantId
  bestBidPriceShort : BitVec 16
  bestBidSizeShort : BitVec 16
  deriving DecidableEq, Repr

namespace NationalBestBidShortAppendage

def encode (message : NationalBestBidShortAppendage) : List UInt8 :=
  BestBidParticipantId.encode message.bestBidParticipantId
    ++ (encodeUInt 2 message.bestBidPriceShort
    ++ (encodeUInt 2 message.bestBidSizeShort))

def decode (bytes : List UInt8) : Option (NationalBestBidShortAppendage × List UInt8) := do
  let (bestBidParticipantId, bytes) ← BestBidParticipantId.decode bytes
  let (bestBidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bestBidSizeShort, bytes) ← decodeUInt 2 bytes
  pure ({ bestBidParticipantId, bestBidPriceShort, bestBidSizeShort }, bytes)

@[simp] theorem encode_length (message : NationalBestBidShortAppendage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, BestBidParticipantId.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NationalBestBidShortAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NationalBestBidShortAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, BestBidParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NationalBestBidShortAppendage

/-- National Best Offer Short Appendage: 5 bytes -/
structure NationalBestOfferShortAppendage where
  bestOfferParticipantId : BestOfferParticipantId
  bestOfferPriceShort : BitVec 16
  bestOfferSizeShort : BitVec 16
  deriving DecidableEq, Repr

namespace NationalBestOfferShortAppendage

def encode (message : NationalBestOfferShortAppendage) : List UInt8 :=
  BestOfferParticipantId.encode message.bestOfferParticipantId
    ++ (encodeUInt 2 message.bestOfferPriceShort
    ++ (encodeUInt 2 message.bestOfferSizeShort))

def decode (bytes : List UInt8) : Option (NationalBestOfferShortAppendage × List UInt8) := do
  let (bestOfferParticipantId, bytes) ← BestOfferParticipantId.decode bytes
  let (bestOfferPriceShort, bytes) ← decodeUInt 2 bytes
  let (bestOfferSizeShort, bytes) ← decodeUInt 2 bytes
  pure ({ bestOfferParticipantId, bestOfferPriceShort, bestOfferSizeShort }, bytes)

@[simp] theorem encode_length (message : NationalBestOfferShortAppendage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, BestOfferParticipantId.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NationalBestOfferShortAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NationalBestOfferShortAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, BestOfferParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NationalBestOfferShortAppendage

/-- National Best Bid Short Appendage: 10 bytes -/
structure NationalBestBidShortAppendageNationalBestOfferShortAppendage where
  nationalBestBidShortAppendage : NationalBestBidShortAppendage
  nationalBestOfferShortAppendage : NationalBestOfferShortAppendage
  deriving DecidableEq, Repr

namespace NationalBestBidShortAppendageNationalBestOfferShortAppendage

def encode (message : NationalBestBidShortAppendageNationalBestOfferShortAppendage) : List UInt8 :=
  NationalBestBidShortAppendage.encode message.nationalBestBidShortAppendage
    ++ (NationalBestOfferShortAppendage.encode message.nationalBestOfferShortAppendage)

def decode (bytes : List UInt8) : Option (NationalBestBidShortAppendageNationalBestOfferShortAppendage × List UInt8) := do
  let (nationalBestBidShortAppendage, bytes) ← NationalBestBidShortAppendage.decode bytes
  let (nationalBestOfferShortAppendage, bytes) ← NationalBestOfferShortAppendage.decode bytes
  pure ({ nationalBestBidShortAppendage, nationalBestOfferShortAppendage }, bytes)

@[simp] theorem encode_length (message : NationalBestBidShortAppendageNationalBestOfferShortAppendage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, NationalBestBidShortAppendage.encode_length, NationalBestOfferShortAppendage.encode_length]

theorem encode_length_pos (message : NationalBestBidShortAppendageNationalBestOfferShortAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NationalBestBidShortAppendageNationalBestOfferShortAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, NationalBestBidShortAppendage.decode_encode, some_bind]
  dsimp only
  rw [NationalBestOfferShortAppendage.decode_encode, some_bind]
  rfl

end NationalBestBidShortAppendageNationalBestOfferShortAppendage

/-- National Bbo Indicator: 0 bytes -/
structure NationalBboAbsent where
  deriving DecidableEq, Repr

namespace NationalBboAbsent

def encode (_ : NationalBboAbsent) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (NationalBboAbsent × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : NationalBboAbsent) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : NationalBboAbsent) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end NationalBboAbsent

/-- The National Best Bid Long Appendage or National Best Offer Long Appendage or National Best Bid Short Appendage or National Best Offer Short Appendage the National Bbo Indicator says is attached, or none -/
inductive NationalBboChoice where
  | nationalBestBidLongAppendageNationalBestOfferLongAppendage (message : NationalBestBidLongAppendageNationalBestOfferLongAppendage) -- "U" 0x55
  | nationalBestBidShortAppendageNationalBestOfferShortAppendage (message : NationalBestBidShortAppendageNationalBestOfferShortAppendage) -- "T" 0x54
  | notIncluded (message : NationalBboAbsent) -- " " 0x20
  | noBestBidChangeOrBestOfferChange (message : NationalBboAbsent) -- "A" 0x41
  | noBestBidChangeQuoteContainsBestOffer (message : NationalBboAbsent) -- "B" 0x42
  | noBestBidChangeBestOfferShortAppendage (message : NationalBboAbsent) -- "C" 0x43
  | noBestBidChangeBestOfferLongAppendage (message : NationalBboAbsent) -- "D" 0x44
  | noBestBidChangeNoBestOffer (message : NationalBboAbsent) -- "E" 0x45
  | quoteContainsBestBidNoBestOfferChange (message : NationalBboAbsent) -- "F" 0x46
  | quoteContainsBestBidQuoteContainsBestOffer (message : NationalBboAbsent) -- "G" 0x47
  | quoteContainsBestBidBestOfferShortAppendage (message : NationalBboAbsent) -- "H" 0x48
  | quoteContainsBestBidBestOfferLongAppendage (message : NationalBboAbsent) -- "I" 0x49
  | quoteContainsBestBidNoBestOffer (message : NationalBboAbsent) -- "J" 0x4A
  | noBestBidNoBestOfferChange (message : NationalBboAbsent) -- "K" 0x4B
  | noBestBidQuoteContainsBestOffer (message : NationalBboAbsent) -- "L" 0x4C
  | noBestBidBestOfferShortAppendage (message : NationalBboAbsent) -- "M" 0x4D
  | noBestBidBestOfferLongAppendage (message : NationalBboAbsent) -- "N" 0x4E
  | noBestBidNoBestOffer (message : NationalBboAbsent) -- "O" 0x4F
  | bestBidShortAppendageNoBestOfferChange (message : NationalBboAbsent) -- "P" 0x50
  | bestBidLongAppendageNoBestOfferChange (message : NationalBboAbsent) -- "Q" 0x51
  | bestBidShortAppendageQuoteContainsBestOffer (message : NationalBboAbsent) -- "R" 0x52
  | bestBidLongAppendageQuoteContainsBestOffer (message : NationalBboAbsent) -- "S" 0x53
  | bestBidShortAppendageNoBestOffer (message : NationalBboAbsent) -- "V" 0x56
  | bestBidLongAppendageNoBestOffer (message : NationalBboAbsent) -- "W" 0x57
  deriving DecidableEq, Repr

namespace NationalBboChoice

/-- The National Bbo Indicator each message is sent under -/
def tag : NationalBboChoice → BitVec 8
  | .nationalBestBidLongAppendageNationalBestOfferLongAppendage _ => 85
  | .nationalBestBidShortAppendageNationalBestOfferShortAppendage _ => 84
  | .notIncluded _ => 32
  | .noBestBidChangeOrBestOfferChange _ => 65
  | .noBestBidChangeQuoteContainsBestOffer _ => 66
  | .noBestBidChangeBestOfferShortAppendage _ => 67
  | .noBestBidChangeBestOfferLongAppendage _ => 68
  | .noBestBidChangeNoBestOffer _ => 69
  | .quoteContainsBestBidNoBestOfferChange _ => 70
  | .quoteContainsBestBidQuoteContainsBestOffer _ => 71
  | .quoteContainsBestBidBestOfferShortAppendage _ => 72
  | .quoteContainsBestBidBestOfferLongAppendage _ => 73
  | .quoteContainsBestBidNoBestOffer _ => 74
  | .noBestBidNoBestOfferChange _ => 75
  | .noBestBidQuoteContainsBestOffer _ => 76
  | .noBestBidBestOfferShortAppendage _ => 77
  | .noBestBidBestOfferLongAppendage _ => 78
  | .noBestBidNoBestOffer _ => 79
  | .bestBidShortAppendageNoBestOfferChange _ => 80
  | .bestBidLongAppendageNoBestOfferChange _ => 81
  | .bestBidShortAppendageQuoteContainsBestOffer _ => 82
  | .bestBidLongAppendageQuoteContainsBestOffer _ => 83
  | .bestBidShortAppendageNoBestOffer _ => 86
  | .bestBidLongAppendageNoBestOffer _ => 87

def encode : NationalBboChoice → List UInt8
  | .nationalBestBidLongAppendageNationalBestOfferLongAppendage message => NationalBestBidLongAppendageNationalBestOfferLongAppendage.encode message
  | .nationalBestBidShortAppendageNationalBestOfferShortAppendage message => NationalBestBidShortAppendageNationalBestOfferShortAppendage.encode message
  | .notIncluded message => NationalBboAbsent.encode message
  | .noBestBidChangeOrBestOfferChange message => NationalBboAbsent.encode message
  | .noBestBidChangeQuoteContainsBestOffer message => NationalBboAbsent.encode message
  | .noBestBidChangeBestOfferShortAppendage message => NationalBboAbsent.encode message
  | .noBestBidChangeBestOfferLongAppendage message => NationalBboAbsent.encode message
  | .noBestBidChangeNoBestOffer message => NationalBboAbsent.encode message
  | .quoteContainsBestBidNoBestOfferChange message => NationalBboAbsent.encode message
  | .quoteContainsBestBidQuoteContainsBestOffer message => NationalBboAbsent.encode message
  | .quoteContainsBestBidBestOfferShortAppendage message => NationalBboAbsent.encode message
  | .quoteContainsBestBidBestOfferLongAppendage message => NationalBboAbsent.encode message
  | .quoteContainsBestBidNoBestOffer message => NationalBboAbsent.encode message
  | .noBestBidNoBestOfferChange message => NationalBboAbsent.encode message
  | .noBestBidQuoteContainsBestOffer message => NationalBboAbsent.encode message
  | .noBestBidBestOfferShortAppendage message => NationalBboAbsent.encode message
  | .noBestBidBestOfferLongAppendage message => NationalBboAbsent.encode message
  | .noBestBidNoBestOffer message => NationalBboAbsent.encode message
  | .bestBidShortAppendageNoBestOfferChange message => NationalBboAbsent.encode message
  | .bestBidLongAppendageNoBestOfferChange message => NationalBboAbsent.encode message
  | .bestBidShortAppendageQuoteContainsBestOffer message => NationalBboAbsent.encode message
  | .bestBidLongAppendageQuoteContainsBestOffer message => NationalBboAbsent.encode message
  | .bestBidShortAppendageNoBestOffer message => NationalBboAbsent.encode message
  | .bestBidLongAppendageNoBestOffer message => NationalBboAbsent.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : NationalBboChoice) : (encode message).length ≤ 36 := by
  cases message with
  | nationalBestBidLongAppendageNationalBestOfferLongAppendage inner =>
    simp only [encode, NationalBestBidLongAppendageNationalBestOfferLongAppendage.encode_length]
    omega
  | nationalBestBidShortAppendageNationalBestOfferShortAppendage inner =>
    simp only [encode, NationalBestBidShortAppendageNationalBestOfferShortAppendage.encode_length]
    omega
  | notIncluded inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeOrBestOfferChange inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeQuoteContainsBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferShortAppendage inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferLongAppendage inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOfferChange inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidQuoteContainsBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidBestOfferShortAppendage inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidBestOfferLongAppendage inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOfferChange inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidQuoteContainsBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferShortAppendage inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferLongAppendage inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageNoBestOfferChange inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageNoBestOfferChange inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageQuoteContainsBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageQuoteContainsBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageNoBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageNoBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (NationalBboChoice × List UInt8) :=
  if tag = 85 then (NationalBestBidLongAppendageNationalBestOfferLongAppendage.decode bytes).map fun (message, rest) => (.nationalBestBidLongAppendageNationalBestOfferLongAppendage message, rest)
  else if tag = 84 then (NationalBestBidShortAppendageNationalBestOfferShortAppendage.decode bytes).map fun (message, rest) => (.nationalBestBidShortAppendageNationalBestOfferShortAppendage message, rest)
  else if tag = 32 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.notIncluded message, rest)
  else if tag = 65 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidChangeOrBestOfferChange message, rest)
  else if tag = 66 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidChangeQuoteContainsBestOffer message, rest)
  else if tag = 67 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidChangeBestOfferShortAppendage message, rest)
  else if tag = 68 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidChangeBestOfferLongAppendage message, rest)
  else if tag = 69 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidChangeNoBestOffer message, rest)
  else if tag = 70 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.quoteContainsBestBidNoBestOfferChange message, rest)
  else if tag = 71 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.quoteContainsBestBidQuoteContainsBestOffer message, rest)
  else if tag = 72 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.quoteContainsBestBidBestOfferShortAppendage message, rest)
  else if tag = 73 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.quoteContainsBestBidBestOfferLongAppendage message, rest)
  else if tag = 74 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.quoteContainsBestBidNoBestOffer message, rest)
  else if tag = 75 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidNoBestOfferChange message, rest)
  else if tag = 76 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidQuoteContainsBestOffer message, rest)
  else if tag = 77 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidBestOfferShortAppendage message, rest)
  else if tag = 78 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidBestOfferLongAppendage message, rest)
  else if tag = 79 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidNoBestOffer message, rest)
  else if tag = 80 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.bestBidShortAppendageNoBestOfferChange message, rest)
  else if tag = 81 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.bestBidLongAppendageNoBestOfferChange message, rest)
  else if tag = 82 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.bestBidShortAppendageQuoteContainsBestOffer message, rest)
  else if tag = 83 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.bestBidLongAppendageQuoteContainsBestOffer message, rest)
  else if tag = 86 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.bestBidShortAppendageNoBestOffer message, rest)
  else if tag = 87 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.bestBidLongAppendageNoBestOffer message, rest)
  else none

@[simp] theorem decode_encode (message : NationalBboChoice) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end NationalBboChoice

/-- Long Quote Message -/
structure LongQuoteMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbolLong : Alpha 11
  instrumentType : InstrumentType
  quoteCondition : QuoteCondition
  securityStatusIndicator : SecurityStatusIndicator
  bidPriceLowerLimitPriceBand : BitVec 64
  bidSizeLong : BitVec 32
  offerPriceUpperLimitPriceBand : BitVec 64
  offerSizeLong : BitVec 32
  retailInterestIndicator : RetailInterestIndicator
  settlementCondition : SettlementCondition
  marketCondition : MarketCondition
  finraMarketMakerId : Alpha 4
  finraBboIndicator : FinraBboIndicator
  adfTimestamp : AdfTimestamp
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  sipGeneratedMessageIdentifier : SipGeneratedMessageIdentifier
  luldIndicator : Alpha 1
  nationalBboLuldIndicator : NationalBboLuldIndicator
  nationalBboChoice : NationalBboChoice
  deriving DecidableEq, Repr

namespace LongQuoteMessage

def encode (message : LongQuoteMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbolLong
    ++ (InstrumentType.encode message.instrumentType
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (SecurityStatusIndicator.encode message.securityStatusIndicator
    ++ (encodeUInt 8 message.bidPriceLowerLimitPriceBand
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 8 message.offerPriceUpperLimitPriceBand
    ++ (encodeUInt 4 message.offerSizeLong
    ++ (RetailInterestIndicator.encode message.retailInterestIndicator
    ++ (SettlementCondition.encode message.settlementCondition
    ++ (MarketCondition.encode message.marketCondition
    ++ (Alpha.encode message.finraMarketMakerId
    ++ (FinraBboIndicator.encode message.finraBboIndicator
    ++ (AdfTimestamp.encode message.adfTimestamp
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (SipGeneratedMessageIdentifier.encode message.sipGeneratedMessageIdentifier
    ++ (Alpha.encode message.luldIndicator
    ++ (NationalBboLuldIndicator.encode message.nationalBboLuldIndicator
    ++ (encodeUInt 1 (NationalBboChoice.tag message.nationalBboChoice)
    ++ (NationalBboChoice.encode message.nationalBboChoice))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (LongQuoteMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbolLong, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (securityStatusIndicator, bytes) ← SecurityStatusIndicator.decode bytes
  let (bidPriceLowerLimitPriceBand, bytes) ← decodeUInt 8 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (offerPriceUpperLimitPriceBand, bytes) ← decodeUInt 8 bytes
  let (offerSizeLong, bytes) ← decodeUInt 4 bytes
  let (retailInterestIndicator, bytes) ← RetailInterestIndicator.decode bytes
  let (settlementCondition, bytes) ← SettlementCondition.decode bytes
  let (marketCondition, bytes) ← MarketCondition.decode bytes
  let (finraMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBboIndicator, bytes) ← FinraBboIndicator.decode bytes
  let (adfTimestamp, bytes) ← AdfTimestamp.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (sipGeneratedMessageIdentifier, bytes) ← SipGeneratedMessageIdentifier.decode bytes
  let (luldIndicator, bytes) ← Alpha.decode 1 bytes
  let (nationalBboLuldIndicator, bytes) ← NationalBboLuldIndicator.decode bytes
  let (nationalBboIndicator, bytes) ← decodeUInt 1 bytes
  let (nationalBboChoice, bytes) ← NationalBboChoice.decode nationalBboIndicator bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber, securitySymbolLong, instrumentType, quoteCondition, securityStatusIndicator, bidPriceLowerLimitPriceBand, bidSizeLong, offerPriceUpperLimitPriceBand, offerSizeLong, retailInterestIndicator, settlementCondition, marketCondition, finraMarketMakerId, finraBboIndicator, adfTimestamp, shortSaleRestrictionIndicator, primaryListingMarketParticipantId, financialStatusIndicator, sipGeneratedMessageIdentifier, luldIndicator, nationalBboLuldIndicator, nationalBboChoice }, bytes)

theorem encode_length_pos (message : LongQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ParticipantId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongQuoteMessage) : (encode message).length ≤ 119 := by
  unfold encode
  cases message.nationalBboChoice with
  | nationalBestBidLongAppendageNationalBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBestBidLongAppendageNationalBestOfferLongAppendage.encode_length]
    omega
  | nationalBestBidShortAppendageNationalBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBestBidShortAppendageNationalBestOfferShortAppendage.encode_length]
    omega
  | notIncluded inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeOrBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : LongQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityStatusIndicator.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinraBboIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AdfTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SipGeneratedMessageIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NationalBboLuldIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [NationalBboChoice.decode_encode, some_bind]
  rfl

end LongQuoteMessage

/-- Short Quote Message -/
structure ShortQuoteMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbolShort : Alpha 5
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  offerPriceShort : BitVec 16
  offerSizeShort : BitVec 16
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  nationalBboChoice : NationalBboChoice
  deriving DecidableEq, Repr

namespace ShortQuoteMessage

def encode (message : ShortQuoteMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbolShort
    ++ (encodeUInt 2 message.bidPriceShort
    ++ (encodeUInt 2 message.bidSizeShort
    ++ (encodeUInt 2 message.offerPriceShort
    ++ (encodeUInt 2 message.offerSizeShort
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (encodeUInt 1 (NationalBboChoice.tag message.nationalBboChoice)
    ++ (NationalBboChoice.encode message.nationalBboChoice))))))))))))

def decode (bytes : List UInt8) : Option (ShortQuoteMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbolShort, bytes) ← Alpha.decode 5 bytes
  let (bidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bidSizeShort, bytes) ← decodeUInt 2 bytes
  let (offerPriceShort, bytes) ← decodeUInt 2 bytes
  let (offerSizeShort, bytes) ← decodeUInt 2 bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (nationalBboIndicator, bytes) ← decodeUInt 1 bytes
  let (nationalBboChoice, bytes) ← NationalBboChoice.decode nationalBboIndicator bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber, securitySymbolShort, bidPriceShort, bidSizeShort, offerPriceShort, offerSizeShort, primaryListingMarketParticipantId, nationalBboChoice }, bytes)

theorem encode_length_pos (message : ShortQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ParticipantId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ShortQuoteMessage) : (encode message).length ≤ 73 := by
  unfold encode
  cases message.nationalBboChoice with
  | nationalBestBidLongAppendageNationalBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBestBidLongAppendageNationalBestOfferLongAppendage.encode_length]
    omega
  | nationalBestBidShortAppendageNationalBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBestBidShortAppendageNationalBestOfferShortAppendage.encode_length]
    omega
  | notIncluded inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeOrBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega

@[simp] theorem decode_encode (message : ShortQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [NationalBboChoice.decode_encode, some_bind]
  rfl

end ShortQuoteMessage

/-- Special Long Quote Message -/
structure SpecialLongQuoteMessage where
  participantId : ParticipantId
  participantTimestamp : ParticipantTimestamp
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbolLong : Alpha 11
  instrumentType : InstrumentType
  quoteCondition : QuoteCondition
  securityStatusIndicator : SecurityStatusIndicator
  bidPriceLong : BitVec 64
  bidSizeLong : BitVec 32
  offerPriceLong : BitVec 64
  offerSizeLong : BitVec 32
  retailInterestIndicator : RetailInterestIndicator
  settlementCondition : SettlementCondition
  marketCondition : MarketCondition
  finraMarketMakerId : Alpha 4
  finraBestBidQuoteCondition : Alpha 1
  finraBestBidPrice : BitVec 64
  finraBestBidSize : BitVec 32
  finraBestBidMarketMakerId : Alpha 4
  finraBestOfferQuoteCondition : Alpha 1
  finraBestOfferPrice : BitVec 64
  finraBestOfferSize : BitVec 32
  finraBestOfferMarketMakerId : Alpha 4
  adfTimestamp : AdfTimestamp
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  sipGeneratedMessageIdentifier : SipGeneratedMessageIdentifier
  finraBboLuldIndicator : FinraBboLuldIndicator
  nationalBboLuldIndicator : NationalBboLuldIndicator
  nationalBboChoice : NationalBboChoice
  deriving DecidableEq, Repr

namespace SpecialLongQuoteMessage

def encode (message : SpecialLongQuoteMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (ParticipantTimestamp.encode message.participantTimestamp
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbolLong
    ++ (InstrumentType.encode message.instrumentType
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (SecurityStatusIndicator.encode message.securityStatusIndicator
    ++ (encodeUInt 8 message.bidPriceLong
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 8 message.offerPriceLong
    ++ (encodeUInt 4 message.offerSizeLong
    ++ (RetailInterestIndicator.encode message.retailInterestIndicator
    ++ (SettlementCondition.encode message.settlementCondition
    ++ (MarketCondition.encode message.marketCondition
    ++ (Alpha.encode message.finraMarketMakerId
    ++ (Alpha.encode message.finraBestBidQuoteCondition
    ++ (encodeUInt 8 message.finraBestBidPrice
    ++ (encodeUInt 4 message.finraBestBidSize
    ++ (Alpha.encode message.finraBestBidMarketMakerId
    ++ (Alpha.encode message.finraBestOfferQuoteCondition
    ++ (encodeUInt 8 message.finraBestOfferPrice
    ++ (encodeUInt 4 message.finraBestOfferSize
    ++ (Alpha.encode message.finraBestOfferMarketMakerId
    ++ (AdfTimestamp.encode message.adfTimestamp
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (SipGeneratedMessageIdentifier.encode message.sipGeneratedMessageIdentifier
    ++ (FinraBboLuldIndicator.encode message.finraBboLuldIndicator
    ++ (NationalBboLuldIndicator.encode message.nationalBboLuldIndicator
    ++ (encodeUInt 1 (NationalBboChoice.tag message.nationalBboChoice)
    ++ (NationalBboChoice.encode message.nationalBboChoice)))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpecialLongQuoteMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (participantTimestamp, bytes) ← ParticipantTimestamp.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbolLong, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (securityStatusIndicator, bytes) ← SecurityStatusIndicator.decode bytes
  let (bidPriceLong, bytes) ← decodeUInt 8 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (offerPriceLong, bytes) ← decodeUInt 8 bytes
  let (offerSizeLong, bytes) ← decodeUInt 4 bytes
  let (retailInterestIndicator, bytes) ← RetailInterestIndicator.decode bytes
  let (settlementCondition, bytes) ← SettlementCondition.decode bytes
  let (marketCondition, bytes) ← MarketCondition.decode bytes
  let (finraMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBestBidQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (finraBestBidPrice, bytes) ← decodeUInt 8 bytes
  let (finraBestBidSize, bytes) ← decodeUInt 4 bytes
  let (finraBestBidMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBestOfferQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (finraBestOfferPrice, bytes) ← decodeUInt 8 bytes
  let (finraBestOfferSize, bytes) ← decodeUInt 4 bytes
  let (finraBestOfferMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (adfTimestamp, bytes) ← AdfTimestamp.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (sipGeneratedMessageIdentifier, bytes) ← SipGeneratedMessageIdentifier.decode bytes
  let (finraBboLuldIndicator, bytes) ← FinraBboLuldIndicator.decode bytes
  let (nationalBboLuldIndicator, bytes) ← NationalBboLuldIndicator.decode bytes
  let (nationalBboIndicator, bytes) ← decodeUInt 1 bytes
  let (nationalBboChoice, bytes) ← NationalBboChoice.decode nationalBboIndicator bytes
  pure ({ participantId, participantTimestamp, messageId, transactionId, participantReferenceNumber, securitySymbolLong, instrumentType, quoteCondition, securityStatusIndicator, bidPriceLong, bidSizeLong, offerPriceLong, offerSizeLong, retailInterestIndicator, settlementCondition, marketCondition, finraMarketMakerId, finraBestBidQuoteCondition, finraBestBidPrice, finraBestBidSize, finraBestBidMarketMakerId, finraBestOfferQuoteCondition, finraBestOfferPrice, finraBestOfferSize, finraBestOfferMarketMakerId, adfTimestamp, shortSaleRestrictionIndicator, primaryListingMarketParticipantId, financialStatusIndicator, sipGeneratedMessageIdentifier, finraBboLuldIndicator, nationalBboLuldIndicator, nationalBboChoice }, bytes)

theorem encode_length_pos (message : SpecialLongQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ParticipantId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SpecialLongQuoteMessage) : (encode message).length ≤ 152 := by
  unfold encode
  cases message.nationalBboChoice with
  | nationalBestBidLongAppendageNationalBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestBidLongAppendageNationalBestOfferLongAppendage.encode_length]
    omega
  | nationalBestBidShortAppendageNationalBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestBidShortAppendageNationalBestOfferShortAppendage.encode_length]
    omega
  | notIncluded inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeOrBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, ParticipantTimestamp.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, AdfTimestamp.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpecialLongQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParticipantTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityStatusIndicator.decode_encode, some_bind]
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
  rw [List.append_assoc, AdfTimestamp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SipGeneratedMessageIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinraBboLuldIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NationalBboLuldIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [NationalBboChoice.decode_encode, some_bind]
  rfl

end SpecialLongQuoteMessage

/-- Any Quote Message Payload, selected by Quote Message Type -/
inductive QuoteMessagePayload where
  | auctionStatusMessage (message : AuctionStatusMessage) -- "A" 0x41
  | longQuoteMessage (message : LongQuoteMessage) -- "L" 0x4C
  | shortQuoteMessage (message : ShortQuoteMessage) -- "Q" 0x51
  | specialLongQuoteMessage (message : SpecialLongQuoteMessage) -- "S" 0x53
  deriving DecidableEq, Repr

namespace QuoteMessagePayload

/-- The Quote Message Type each message is sent under -/
def tag : QuoteMessagePayload → BitVec 8
  | .auctionStatusMessage _ => 65
  | .longQuoteMessage _ => 76
  | .shortQuoteMessage _ => 81
  | .specialLongQuoteMessage _ => 83

def encode : QuoteMessagePayload → List UInt8
  | .auctionStatusMessage message => AuctionStatusMessage.encode message
  | .longQuoteMessage message => LongQuoteMessage.encode message
  | .shortQuoteMessage message => ShortQuoteMessage.encode message
  | .specialLongQuoteMessage message => SpecialLongQuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : QuoteMessagePayload) : (encode message).length ≤ 152 := by
  cases message with
  | auctionStatusMessage inner =>
    simp only [encode, AuctionStatusMessage.encode_length]
    omega
  | longQuoteMessage inner =>
    have bound_inner := LongQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | shortQuoteMessage inner =>
    have bound_inner := ShortQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | specialLongQuoteMessage inner =>
    have bound_inner := SpecialLongQuoteMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (QuoteMessagePayload × List UInt8) :=
  if tag = 65 then (AuctionStatusMessage.decode bytes).map fun (message, rest) => (.auctionStatusMessage message, rest)
  else if tag = 76 then (LongQuoteMessage.decode bytes).map fun (message, rest) => (.longQuoteMessage message, rest)
  else if tag = 81 then (ShortQuoteMessage.decode bytes).map fun (message, rest) => (.shortQuoteMessage message, rest)
  else if tag = 83 then (SpecialLongQuoteMessage.decode bytes).map fun (message, rest) => (.specialLongQuoteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : QuoteMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end QuoteMessagePayload

/-- Quote Message -/
structure QuoteMessage where
  quoteMessagePayload : QuoteMessagePayload
  deriving DecidableEq, Repr

namespace QuoteMessage

def encode (message : QuoteMessage) : List UInt8 :=
  encodeUInt 1 (QuoteMessagePayload.tag message.quoteMessagePayload)
    ++ (QuoteMessagePayload.encode message.quoteMessagePayload)

def decode (bytes : List UInt8) : Option (QuoteMessage × List UInt8) := do
  let (quoteMessageType, bytes) ← decodeUInt 1 bytes
  let (quoteMessagePayload, bytes) ← QuoteMessagePayload.decode quoteMessageType bytes
  pure ({ quoteMessagePayload }, bytes)

theorem encode_length_pos (message : QuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteMessage) : (encode message).length ≤ 153 := by
  unfold encode
  cases message.quoteMessagePayload with
  | auctionStatusMessage inner =>
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length, AuctionStatusMessage.encode_length]
    omega
  | longQuoteMessage inner =>
    have bound_inner := LongQuoteMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | shortQuoteMessage inner =>
    have bound_inner := ShortQuoteMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | specialLongQuoteMessage inner =>
    have bound_inner := SpecialLongQuoteMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : QuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [QuoteMessagePayload.decode_encode, some_bind]
  rfl

end QuoteMessage

/-- Any Category Payload, selected by Message Category -/
inductive CategoryPayload where
  | administrativeMessage (message : AdministrativeMessage) -- "A" 0x41
  | controlMessage (message : ControlMessage) -- "C" 0x43
  | marketStatusMessage (message : MarketStatusMessage) -- "M" 0x4D
  | quoteMessage (message : QuoteMessage) -- "Q" 0x51
  deriving DecidableEq, Repr

namespace CategoryPayload

/-- The Message Category each message is sent under -/
def tag : CategoryPayload → BitVec 8
  | .administrativeMessage _ => 65
  | .controlMessage _ => 67
  | .marketStatusMessage _ => 77
  | .quoteMessage _ => 81

def encode : CategoryPayload → List UInt8
  | .administrativeMessage message => AdministrativeMessage.encode message
  | .controlMessage message => ControlMessage.encode message
  | .marketStatusMessage message => MarketStatusMessage.encode message
  | .quoteMessage message => QuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : CategoryPayload) : (encode message).length ≤ 153 := by
  cases message with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega
  | controlMessage inner =>
    have bound_inner := ControlMessage.encode_length_le inner
    simp only [encode]
    omega
  | marketStatusMessage inner =>
    have bound_inner := MarketStatusMessage.encode_length_le inner
    simp only [encode]
    omega
  | quoteMessage inner =>
    have bound_inner := QuoteMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (CategoryPayload × List UInt8) :=
  if tag = 65 then (AdministrativeMessage.decode bytes).map fun (message, rest) => (.administrativeMessage message, rest)
  else if tag = 67 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage message, rest)
  else if tag = 77 then (MarketStatusMessage.decode bytes).map fun (message, rest) => (.marketStatusMessage message, rest)
  else if tag = 81 then (QuoteMessage.decode bytes).map fun (message, rest) => (.quoteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : CategoryPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end CategoryPayload

/-- Message -/
structure Message where
  messageLength : BitVec 16
  categoryPayload : CategoryPayload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUInt 2 message.messageLength
    ++ (encodeUInt 1 (CategoryPayload.tag message.categoryPayload)
    ++ (CategoryPayload.encode message.categoryPayload))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (messageCategory, bytes) ← decodeUInt 1 bytes
  let (categoryPayload, bytes) ← CategoryPayload.decode messageCategory bytes
  pure ({ messageLength, categoryPayload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 156 := by
  unfold encode
  cases message.categoryPayload with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | controlMessage inner =>
    have bound_inner := ControlMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | marketStatusMessage inner =>
    have bound_inner := MarketStatusMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | quoteMessage inner =>
    have bound_inner := QuoteMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CategoryPayload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  version : BitVec 8
  blockSize : BitVec 16
  dataFeedIndicator : Alpha 1
  retransmissionIndicator : RetransmissionIndicator
  blockSequenceNumber : BitVec 32
  sipBlockTimestamp : SipBlockTimestamp
  blockChecksum : BitVec 16
  message : Bounded 1 Message
  blockPadByte : Capped 1
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.version
    ++ (encodeUInt 2 message.blockSize
    ++ (Alpha.encode message.dataFeedIndicator
    ++ (RetransmissionIndicator.encode message.retransmissionIndicator
    ++ (encodeUInt 4 message.blockSequenceNumber
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (SipBlockTimestamp.encode message.sipBlockTimestamp
    ++ (encodeUInt 2 message.blockChecksum
    ++ (encodeMany Message.encode message.message.val
    ++ (message.blockPadByte.val)))))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (version, bytes) ← decodeUInt 1 bytes
  let (blockSize, bytes) ← decodeUInt 2 bytes
  let (dataFeedIndicator, bytes) ← Alpha.decode 1 bytes
  let (retransmissionIndicator, bytes) ← RetransmissionIndicator.decode bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (messagesInBlock, bytes) ← decodeUInt 1 bytes
  let (sipBlockTimestamp, bytes) ← SipBlockTimestamp.decode bytes
  let (blockChecksum, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messagesInBlock.toNat bytes
  let blockPadByte_ := bytes
  if fits_message : message_.length < 256 ^ 1 then
    if fits_blockPadByte : blockPadByte_.length ≤ 1 then
      pure { version, blockSize, dataFeedIndicator, retransmissionIndicator, blockSequenceNumber, sipBlockTimestamp, blockChecksum, message := ⟨message_, fits_message⟩, blockPadByte := ⟨blockPadByte_, fits_blockPadByte⟩ }
    else none
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 39801 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 156 Message.encode_length_le message.message.val
  have bound_blockPadByte := message.blockPadByte.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIndicator.encode_length, SipBlockTimestamp.encode_length]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [RetransmissionIndicator.decode_encode, some_bind]
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

end Omi.SiacCqsOutputCtaV191
