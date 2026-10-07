import Wire

/-!
# The Securities Industry Automation Corporation Snapshot v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Block Pad Byte pads to a 2 byte boundary: it is read as the bytes left to the end of the frame, fewer than 2, and the frame's length is trusted to keep the boundary.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.SiacCqsSnapshotCtaV10

/-- Participant Id: one byte code -/
def ParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive ParticipantId where
  | nyseAmerican -- Nyse American
  | nasdaqBx -- Nasdaq Bx
  | nyseNational -- Nyse National
  | adf -- Adf
  | miax -- Miax
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseChicago -- Nyse Chicago
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | cqs -- Cqs
  | nasdaq -- Nasdaq
  | memx -- Memx
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
  | .adf => 0x44
  | .miax => 0x48
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseChicago => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .cqs => 0x53
  | .nasdaq => 0x54
  | .memx => 0x55
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
  else if byte = 0x44 then .adf
  else if byte = 0x48 then .miax
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x53 then .cqs
  else if byte = 0x54 then .nasdaq
  else if byte = 0x55 then .memx
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
  | adf => decide
  | miax => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseChicago => decide
  | nyse => decide
  | nyseArca => decide
  | cqs => decide
  | nasdaq => decide
  | memx => decide
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

/-- National Best Bid Participant Id: one byte code -/
def NationalBestBidParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive NationalBestBidParticipantId where
  | nyseAmerican -- Nyse American
  | nasdaqBx -- Nasdaq Bx
  | nyseNational -- Nyse National
  | adf -- Adf
  | miax -- Miax
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseChicago -- Nyse Chicago
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | cqs -- Cqs
  | nasdaq -- Nasdaq
  | memx -- Memx
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqPsx -- Nasdaq Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | unlisted (byte : { byte : UInt8 // byte ∉ NationalBestBidParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NationalBestBidParticipantId

def toByte : NationalBestBidParticipantId → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqBx => 0x42
  | .nyseNational => 0x43
  | .adf => 0x44
  | .miax => 0x48
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseChicago => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .cqs => 0x53
  | .nasdaq => 0x54
  | .memx => 0x55
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NationalBestBidParticipantId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .adf
  else if byte = 0x48 then .miax
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x53 then .cqs
  else if byte = 0x54 then .nasdaq
  else if byte = 0x55 then .memx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqPsx
  else if byte = 0x59 then .cboeByx
  else .cboeBzx

def ofByte (byte : UInt8) : NationalBestBidParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NationalBestBidParticipantId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqBx => decide
  | nyseNational => decide
  | adf => decide
  | miax => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseChicago => decide
  | nyse => decide
  | nyseArca => decide
  | cqs => decide
  | nasdaq => decide
  | memx => decide
  | iex => decide
  | cbsx => decide
  | nasdaqPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NationalBestBidParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NationalBestBidParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NationalBestBidParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NationalBestBidParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NationalBestBidParticipantId

/-- National Best Bid Quote Condition: one byte code -/
def NationalBestBidQuoteCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x45, 0x46, 0x48, 0x4C, 0x4E, 0x4F, 0x52, 0x55, 0x57, 0x34]

inductive NationalBestBidQuoteCondition where
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
  | unlisted (byte : { byte : UInt8 // byte ∉ NationalBestBidQuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NationalBestBidQuoteCondition

def toByte : NationalBestBidQuoteCondition → UInt8
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
def listed (byte : UInt8) : NationalBestBidQuoteCondition :=
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

def ofByte (byte : UInt8) : NationalBestBidQuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NationalBestBidQuoteCondition) : ofByte value.toByte = value := by
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

def encode (value : NationalBestBidQuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NationalBestBidQuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NationalBestBidQuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NationalBestBidQuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NationalBestBidQuoteCondition

/-- National Best Offer Participant Id: one byte code -/
def NationalBestOfferParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive NationalBestOfferParticipantId where
  | nyseAmerican -- Nyse American
  | nasdaqBx -- Nasdaq Bx
  | nyseNational -- Nyse National
  | adf -- Adf
  | miax -- Miax
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseChicago -- Nyse Chicago
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | cqs -- Cqs
  | nasdaq -- Nasdaq
  | memx -- Memx
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqPsx -- Nasdaq Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | unlisted (byte : { byte : UInt8 // byte ∉ NationalBestOfferParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NationalBestOfferParticipantId

def toByte : NationalBestOfferParticipantId → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqBx => 0x42
  | .nyseNational => 0x43
  | .adf => 0x44
  | .miax => 0x48
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseChicago => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .cqs => 0x53
  | .nasdaq => 0x54
  | .memx => 0x55
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NationalBestOfferParticipantId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .adf
  else if byte = 0x48 then .miax
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x53 then .cqs
  else if byte = 0x54 then .nasdaq
  else if byte = 0x55 then .memx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqPsx
  else if byte = 0x59 then .cboeByx
  else .cboeBzx

def ofByte (byte : UInt8) : NationalBestOfferParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NationalBestOfferParticipantId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqBx => decide
  | nyseNational => decide
  | adf => decide
  | miax => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseChicago => decide
  | nyse => decide
  | nyseArca => decide
  | cqs => decide
  | nasdaq => decide
  | memx => decide
  | iex => decide
  | cbsx => decide
  | nasdaqPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NationalBestOfferParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NationalBestOfferParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NationalBestOfferParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NationalBestOfferParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NationalBestOfferParticipantId

/-- National Best Offer Quote Condition: one byte code -/
def NationalBestOfferQuoteCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x45, 0x46, 0x48, 0x4C, 0x4E, 0x4F, 0x52, 0x55, 0x57, 0x34]

inductive NationalBestOfferQuoteCondition where
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
  | unlisted (byte : { byte : UInt8 // byte ∉ NationalBestOfferQuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NationalBestOfferQuoteCondition

def toByte : NationalBestOfferQuoteCondition → UInt8
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
def listed (byte : UInt8) : NationalBestOfferQuoteCondition :=
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

def ofByte (byte : UInt8) : NationalBestOfferQuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NationalBestOfferQuoteCondition) : ofByte value.toByte = value := by
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

def encode (value : NationalBestOfferQuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NationalBestOfferQuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NationalBestOfferQuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NationalBestOfferQuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NationalBestOfferQuoteCondition

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

/-- Primary Listing Market Participant Id: one byte code -/
def PrimaryListingMarketParticipantId.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive PrimaryListingMarketParticipantId where
  | notApplicable -- Not Applicable
  | nyseAmerican -- Nyse American
  | nasdaqBx -- Nasdaq Bx
  | nyseNational -- Nyse National
  | adf -- Adf
  | miax -- Miax
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseChicago -- Nyse Chicago
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | memx -- Memx
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqPsx -- Nasdaq Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | unlisted (byte : { byte : UInt8 // byte ∉ PrimaryListingMarketParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrimaryListingMarketParticipantId

def toByte : PrimaryListingMarketParticipantId → UInt8
  | .notApplicable => 0x20
  | .nyseAmerican => 0x41
  | .nasdaqBx => 0x42
  | .nyseNational => 0x43
  | .adf => 0x44
  | .miax => 0x48
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseChicago => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x54
  | .memx => 0x55
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrimaryListingMarketParticipantId :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .adf
  else if byte = 0x48 then .miax
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x54 then .nasdaq
  else if byte = 0x55 then .memx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqPsx
  else if byte = 0x59 then .cboeByx
  else .cboeBzx

def ofByte (byte : UInt8) : PrimaryListingMarketParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrimaryListingMarketParticipantId) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | nyseAmerican => decide
  | nasdaqBx => decide
  | nyseNational => decide
  | adf => decide
  | miax => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseChicago => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | memx => decide
  | iex => decide
  | cbsx => decide
  | nasdaqPsx => decide
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

/-- Halt Reason: one byte code -/
def HaltReason.codes : List UInt8 :=
  [0x20, 0x41, 0x43, 0x44, 0x45, 0x46, 0x49, 0x4D, 0x4E, 0x4F, 0x50, 0x56, 0x58, 0x59, 0x31, 0x32, 0x33]

inductive HaltReason where
  | notApplicable -- Not Applicable
  | additionalInformationRequested -- Additional Information Requested
  | regulatoryConcern -- Regulatory Concern
  | newsReleased -- News Released
  | mergerEffective -- Merger Effective
  | etfComponentPricesNotAvailable -- Etf Component Prices Not Available
  | orderImbalance -- Order Imbalance
  | limitUpLimitDownTradingPause -- Limit Up Limit Down Trading Pause
  | corporateAction -- Corporate Action
  | newSecurityOffering -- New Security Offering
  | newsPending -- News Pending
  | intradayIndicativeValueNotAvailable -- Intraday Indicative Value Not Available
  | operational -- Operational
  | subpennyTrading -- Subpenny Trading
  | marketWideCircuitBreakerLevel1Breached -- Market Wide Circuit Breaker Level 1 Breached
  | marketWideCircuitBreakerLevel2Breached -- Market Wide Circuit Breaker Level 2 Breached
  | marketWideCircuitBreakerLevel3Breached -- Market Wide Circuit Breaker Level 3 Breached
  | unlisted (byte : { byte : UInt8 // byte ∉ HaltReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HaltReason

def toByte : HaltReason → UInt8
  | .notApplicable => 0x20
  | .additionalInformationRequested => 0x41
  | .regulatoryConcern => 0x43
  | .newsReleased => 0x44
  | .mergerEffective => 0x45
  | .etfComponentPricesNotAvailable => 0x46
  | .orderImbalance => 0x49
  | .limitUpLimitDownTradingPause => 0x4D
  | .corporateAction => 0x4E
  | .newSecurityOffering => 0x4F
  | .newsPending => 0x50
  | .intradayIndicativeValueNotAvailable => 0x56
  | .operational => 0x58
  | .subpennyTrading => 0x59
  | .marketWideCircuitBreakerLevel1Breached => 0x31
  | .marketWideCircuitBreakerLevel2Breached => 0x32
  | .marketWideCircuitBreakerLevel3Breached => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HaltReason :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x41 then .additionalInformationRequested
  else if byte = 0x43 then .regulatoryConcern
  else if byte = 0x44 then .newsReleased
  else if byte = 0x45 then .mergerEffective
  else if byte = 0x46 then .etfComponentPricesNotAvailable
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x4D then .limitUpLimitDownTradingPause
  else if byte = 0x4E then .corporateAction
  else if byte = 0x4F then .newSecurityOffering
  else if byte = 0x50 then .newsPending
  else if byte = 0x56 then .intradayIndicativeValueNotAvailable
  else if byte = 0x58 then .operational
  else if byte = 0x59 then .subpennyTrading
  else if byte = 0x31 then .marketWideCircuitBreakerLevel1Breached
  else if byte = 0x32 then .marketWideCircuitBreakerLevel2Breached
  else .marketWideCircuitBreakerLevel3Breached

def ofByte (byte : UInt8) : HaltReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HaltReason) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | additionalInformationRequested => decide
  | regulatoryConcern => decide
  | newsReleased => decide
  | mergerEffective => decide
  | etfComponentPricesNotAvailable => decide
  | orderImbalance => decide
  | limitUpLimitDownTradingPause => decide
  | corporateAction => decide
  | newSecurityOffering => decide
  | newsPending => decide
  | intradayIndicativeValueNotAvailable => decide
  | operational => decide
  | subpennyTrading => decide
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

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x45, 0x46, 0x48, 0x4C, 0x4E, 0x4F, 0x52, 0x55, 0x57, 0x34]

inductive QuoteCondition where
  | notApplicable -- Not Applicable
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
  | .notApplicable => 0x20
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
  if byte = 0x20 then .notApplicable
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
  | notApplicable => decide
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

/-- Luld Indicator: one byte code -/
def LuldIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42]

inductive LuldIndicator where
  | limitUpLimitDownNotApplicable -- Limit Up Limit Down Not Applicable
  | bidIsNonExecutable -- Bid Is Non Executable
  | offerIsNonExecutable -- Offer Is Non Executable
  | unlisted (byte : { byte : UInt8 // byte ∉ LuldIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LuldIndicator

def toByte : LuldIndicator → UInt8
  | .limitUpLimitDownNotApplicable => 0x20
  | .bidIsNonExecutable => 0x41
  | .offerIsNonExecutable => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LuldIndicator :=
  if byte = 0x20 then .limitUpLimitDownNotApplicable
  else if byte = 0x41 then .bidIsNonExecutable
  else .offerIsNonExecutable

def ofByte (byte : UInt8) : LuldIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LuldIndicator) : ofByte value.toByte = value := by
  cases value with
  | limitUpLimitDownNotApplicable => decide
  | bidIsNonExecutable => decide
  | offerIsNonExecutable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LuldIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LuldIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LuldIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LuldIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LuldIndicator

/-- Finra Best Bid Quote Condition: one byte code -/
def FinraBestBidQuoteCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x45, 0x46, 0x48, 0x4C, 0x4E, 0x4F, 0x52, 0x55, 0x57, 0x34]

inductive FinraBestBidQuoteCondition where
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
  | unlisted (byte : { byte : UInt8 // byte ∉ FinraBestBidQuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinraBestBidQuoteCondition

def toByte : FinraBestBidQuoteCondition → UInt8
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
def listed (byte : UInt8) : FinraBestBidQuoteCondition :=
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

def ofByte (byte : UInt8) : FinraBestBidQuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinraBestBidQuoteCondition) : ofByte value.toByte = value := by
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

def encode (value : FinraBestBidQuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinraBestBidQuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FinraBestBidQuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FinraBestBidQuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FinraBestBidQuoteCondition

/-- Finra Best Offer Quote Condition: one byte code -/
def FinraBestOfferQuoteCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x45, 0x46, 0x48, 0x4C, 0x4E, 0x4F, 0x52, 0x55, 0x57, 0x34]

inductive FinraBestOfferQuoteCondition where
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
  | unlisted (byte : { byte : UInt8 // byte ∉ FinraBestOfferQuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinraBestOfferQuoteCondition

def toByte : FinraBestOfferQuoteCondition → UInt8
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
def listed (byte : UInt8) : FinraBestOfferQuoteCondition :=
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

def ofByte (byte : UInt8) : FinraBestOfferQuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinraBestOfferQuoteCondition) : ofByte value.toByte = value := by
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

def encode (value : FinraBestOfferQuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinraBestOfferQuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FinraBestOfferQuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FinraBestOfferQuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FinraBestOfferQuoteCondition

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

/-- Market Wide Circuit Breaker Decline Level Status Snapshot Message: 26 bytes -/
structure MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage where
  participantId : ParticipantId
  mwcbLevel1 : BitVec 64
  mwcbLevel2 : BitVec 64
  mwcbLevel3 : BitVec 64
  reserved : BitVec 8
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage

def encode (message : MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (encodeUInt 8 message.mwcbLevel1
    ++ (encodeUInt 8 message.mwcbLevel2
    ++ (encodeUInt 8 message.mwcbLevel3
    ++ (encodeUInt 1 message.reserved))))

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (mwcbLevel1, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel2, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel3, bytes) ← decodeUInt 8 bytes
  let (reserved, bytes) ← decodeUInt 1 bytes
  pure ({ participantId, mwcbLevel1, mwcbLevel2, mwcbLevel3, reserved }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, encodeUInt_length]

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
  rw [decodeUInt_encodeUInt, some_bind]
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
  nationalBestBidParticipantId : NationalBestBidParticipantId
  nationalBestBidQuoteCondition : NationalBestBidQuoteCondition
  nationalBestBidPrice : BitVec 64
  nationalBestBidSize : BitVec 32
  finraBestBidMarketMakerId : Alpha 4
  nationalBestOfferParticipantId : NationalBestOfferParticipantId
  nationalBestOfferQuoteCondition : NationalBestOfferQuoteCondition
  nationalBestOfferPrice : BitVec 64
  nationalBestOfferSize : BitVec 32
  finraBestOfferMarketMakerId : Alpha 4
  nationalBboLuldIndicator : NationalBboLuldIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  haltReason : HaltReason
  future : Alpha 1
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
    ++ (NationalBestBidParticipantId.encode message.nationalBestBidParticipantId
    ++ (NationalBestBidQuoteCondition.encode message.nationalBestBidQuoteCondition
    ++ (encodeUInt 8 message.nationalBestBidPrice
    ++ (encodeUInt 4 message.nationalBestBidSize
    ++ (Alpha.encode message.finraBestBidMarketMakerId
    ++ (NationalBestOfferParticipantId.encode message.nationalBestOfferParticipantId
    ++ (NationalBestOfferQuoteCondition.encode message.nationalBestOfferQuoteCondition
    ++ (encodeUInt 8 message.nationalBestOfferPrice
    ++ (encodeUInt 4 message.nationalBestOfferSize
    ++ (Alpha.encode message.finraBestOfferMarketMakerId
    ++ (NationalBboLuldIndicator.encode message.nationalBboLuldIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (HaltReason.encode message.haltReason
    ++ (Alpha.encode message.future))))))))))))))))))))))))

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
  let (nationalBestBidParticipantId, bytes) ← NationalBestBidParticipantId.decode bytes
  let (nationalBestBidQuoteCondition, bytes) ← NationalBestBidQuoteCondition.decode bytes
  let (nationalBestBidPrice, bytes) ← decodeUInt 8 bytes
  let (nationalBestBidSize, bytes) ← decodeUInt 4 bytes
  let (finraBestBidMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (nationalBestOfferParticipantId, bytes) ← NationalBestOfferParticipantId.decode bytes
  let (nationalBestOfferQuoteCondition, bytes) ← NationalBestOfferQuoteCondition.decode bytes
  let (nationalBestOfferPrice, bytes) ← decodeUInt 8 bytes
  let (nationalBestOfferSize, bytes) ← decodeUInt 4 bytes
  let (finraBestOfferMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (nationalBboLuldIndicator, bytes) ← NationalBboLuldIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (haltReason, bytes) ← HaltReason.decode bytes
  let (future, bytes) ← Alpha.decode 1 bytes
  pure ({ participantId, securitySymbol, instrumentType, lowerLimitPriceBand, upperLimitPriceBand, auctionCollarReferencePrice, auctionCollarUpperThresholdPrice, auctionCollarLowerThresholdPrice, numberOfExtensions, nationalBestBidParticipantId, nationalBestBidQuoteCondition, nationalBestBidPrice, nationalBestBidSize, finraBestBidMarketMakerId, nationalBestOfferParticipantId, nationalBestOfferQuoteCondition, nationalBestOfferPrice, nationalBestOfferSize, finraBestOfferMarketMakerId, nationalBboLuldIndicator, primaryListingMarketParticipantId, financialStatusIndicator, shortSaleRestrictionIndicator, haltReason, future }, bytes)

@[simp] theorem encode_length (message : ConsolidatedSnapshotMessage) : (encode message).length = 96 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, NationalBestBidParticipantId.encode_length, NationalBestBidQuoteCondition.encode_length, NationalBestOfferParticipantId.encode_length, NationalBestOfferQuoteCondition.encode_length, NationalBboLuldIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, ShortSaleRestrictionIndicator.encode_length, HaltReason.encode_length]

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
  rw [List.append_assoc, NationalBestBidParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NationalBestBidQuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NationalBestOfferParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NationalBestOfferQuoteCondition.decode_encode, some_bind]
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
  luldIndicator : LuldIndicator
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
    ++ (LuldIndicator.encode message.luldIndicator
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
  let (luldIndicator, bytes) ← LuldIndicator.decode bytes
  let (highIndicationPrice, bytes) ← decodeUInt 8 bytes
  let (lowIndicationPrice, bytes) ← decodeUInt 8 bytes
  let (haltReason, bytes) ← HaltReason.decode bytes
  pure ({ participantId, securitySymbol, quoteCondition, bidPrice, bidSize, offerPrice, offerSize, retailInterestIndicator, settlementCondition, marketCondition, luldIndicator, highIndicationPrice, lowIndicationPrice, haltReason }, bytes)

@[simp] theorem encode_length (message : ParticipantSnapshotMessage) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Alpha.encode_length, QuoteCondition.encode_length, encodeUInt_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, LuldIndicator.encode_length, HaltReason.encode_length]

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
  rw [List.append_assoc, LuldIndicator.decode_encode, some_bind]
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
  finraBestBidQuoteCondition : FinraBestBidQuoteCondition
  finraBestBidPrice : BitVec 64
  finraBestBidSize : BitVec 32
  finraBestBidMarketMakerId : Alpha 4
  finraBestOfferQuoteCondition : FinraBestOfferQuoteCondition
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
    ++ (FinraBestBidQuoteCondition.encode message.finraBestBidQuoteCondition
    ++ (encodeUInt 8 message.finraBestBidPrice
    ++ (encodeUInt 4 message.finraBestBidSize
    ++ (Alpha.encode message.finraBestBidMarketMakerId
    ++ (FinraBestOfferQuoteCondition.encode message.finraBestOfferQuoteCondition
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
  let (finraBestBidQuoteCondition, bytes) ← FinraBestBidQuoteCondition.decode bytes
  let (finraBestBidPrice, bytes) ← decodeUInt 8 bytes
  let (finraBestBidSize, bytes) ← decodeUInt 4 bytes
  let (finraBestBidMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBestOfferQuoteCondition, bytes) ← FinraBestOfferQuoteCondition.decode bytes
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
  simp only [List.length_append, ParticipantId.encode_length, Alpha.encode_length, FinraBestBidQuoteCondition.encode_length, encodeUInt_length, FinraBestOfferQuoteCondition.encode_length, FinraBboLuldIndicator.encode_length, HaltReason.encode_length]

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
  rw [List.append_assoc, FinraBestBidQuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinraBestOfferQuoteCondition.decode_encode, some_bind]
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
  | marketWideCircuitBreakerDeclineLevelStatusSnapshotMessage (message : MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage) -- "K" 0x4B
  | consolidatedSnapshotMessage (message : ConsolidatedSnapshotMessage) -- "C" 0x43
  | participantSnapshotMessage (message : ParticipantSnapshotMessage) -- "P" 0x50
  | finraSnapshotMessage (message : FinraSnapshotMessage) -- "F" 0x46
  deriving DecidableEq, Repr

namespace SnapshotMessagePayload

/-- The Snapshot Message Type each message is sent under -/
def tag : SnapshotMessagePayload → BitVec 8
  | .lineIntegrityMessage _ => 84
  | .marketWideCircuitBreakerDeclineLevelStatusSnapshotMessage _ => 75
  | .consolidatedSnapshotMessage _ => 67
  | .participantSnapshotMessage _ => 80
  | .finraSnapshotMessage _ => 70

def encode : SnapshotMessagePayload → List UInt8
  | .lineIntegrityMessage message => LineIntegrityMessage.encode message
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
  | snapshotMessage (message : SnapshotMessage) -- "K" 0x4B
  deriving DecidableEq, Repr

namespace CategoryPayload

/-- The Message Category each message is sent under -/
def tag : CategoryPayload → BitVec 8
  | .snapshotMessage _ => 75

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
  if tag = 75 then (SnapshotMessage.decode bytes).map fun (message, rest) => (.snapshotMessage message, rest)
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
  deliveryFlag : BitVec 8
  lastSeqNum : Alpha 1
  totPubSeqRollover : BitVec 8
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
    ++ (encodeUInt 1 message.deliveryFlag
    ++ (Alpha.encode message.lastSeqNum
    ++ (encodeUInt 1 message.totPubSeqRollover
    ++ (SipBlockTimestamp.encode message.sipBlockTimestamp
    ++ (encodeUInt 2 message.blockChecksum
    ++ (encodeMany Message.encode message.message.val
    ++ (message.blockPadByte.val))))))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (version, bytes) ← decodeUInt 1 bytes
  let (blockSize, bytes) ← decodeUInt 2 bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (messagesInBlock, bytes) ← decodeUInt 1 bytes
  let (deliveryFlag, bytes) ← decodeUInt 1 bytes
  let (lastSeqNum, bytes) ← Alpha.decode 1 bytes
  let (totPubSeqRollover, bytes) ← decodeUInt 1 bytes
  let (sipBlockTimestamp, bytes) ← SipBlockTimestamp.decode bytes
  let (blockChecksum, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messagesInBlock.toNat bytes
  let blockPadByte_ := bytes
  if fits_message : message_.length < 256 ^ 1 then
    if fits_blockPadByte : blockPadByte_.length ≤ 1 then
      pure { version, blockSize, blockSequenceNumber, deliveryFlag, lastSeqNum, totPubSeqRollover, sipBlockTimestamp, blockChecksum, message := ⟨message_, fits_message⟩, blockPadByte := ⟨blockPadByte_, fits_blockPadByte⟩ }
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
  rw [Alpha.decode_encode, some_bind]
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

end Omi.SiacCqsSnapshotCtaV10
