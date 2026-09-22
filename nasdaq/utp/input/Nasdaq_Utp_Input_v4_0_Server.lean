import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v4.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Server Packet's body has no bound its 2 byte Packet Length must fit, so every message carries the proof its own encoding fits: the record is its body with that proof, checked as the frame is read.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqUtpInputUtpV40Server

/-- Cond: one byte code -/
def Cond.codes : List UInt8 :=
  [0x41, 0x42, 0x46, 0x48, 0x49, 0x4C, 0x4E, 0x4F, 0x52, 0x55, 0x58, 0x59, 0x5A, 0x34]

inductive Cond where
  | manualAskAutomatedBid -- Manual Ask Automated Bid
  | manualBidAutomatedAsk -- Manual Bid Automated Ask
  | fastTrading -- Fast Trading
  | manualBidAndAsk -- Manual Bid And Ask
  | orderImbalance -- Order Imbalance
  | closedQuote -- Closed Quote
  | nonfirmQuote -- Nonfirm Quote
  | openingQuoteAutomated -- Opening Quote Automated
  | regularTwosidedOpenQuoteAutomated -- Regular Twosided Open Quote Automated
  | manualBidAndAskNonfirm -- Manual Bid And Ask Nonfirm
  | orderInflux -- Order Influx
  | automatedBidNoOfferOrAutomatedOfferNoBid -- Automated Bid No Offer Or Automated Offer No Bid
  | noOpennoResume -- No Openno Resume
  | intradayAuction -- Intraday Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ Cond.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Cond

def toByte : Cond → UInt8
  | .manualAskAutomatedBid => 0x41
  | .manualBidAutomatedAsk => 0x42
  | .fastTrading => 0x46
  | .manualBidAndAsk => 0x48
  | .orderImbalance => 0x49
  | .closedQuote => 0x4C
  | .nonfirmQuote => 0x4E
  | .openingQuoteAutomated => 0x4F
  | .regularTwosidedOpenQuoteAutomated => 0x52
  | .manualBidAndAskNonfirm => 0x55
  | .orderInflux => 0x58
  | .automatedBidNoOfferOrAutomatedOfferNoBid => 0x59
  | .noOpennoResume => 0x5A
  | .intradayAuction => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Cond :=
  if byte = 0x41 then .manualAskAutomatedBid
  else if byte = 0x42 then .manualBidAutomatedAsk
  else if byte = 0x46 then .fastTrading
  else if byte = 0x48 then .manualBidAndAsk
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x4C then .closedQuote
  else if byte = 0x4E then .nonfirmQuote
  else if byte = 0x4F then .openingQuoteAutomated
  else if byte = 0x52 then .regularTwosidedOpenQuoteAutomated
  else if byte = 0x55 then .manualBidAndAskNonfirm
  else if byte = 0x58 then .orderInflux
  else if byte = 0x59 then .automatedBidNoOfferOrAutomatedOfferNoBid
  else if byte = 0x5A then .noOpennoResume
  else .intradayAuction

def ofByte (byte : UInt8) : Cond :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Cond) : ofByte value.toByte = value := by
  cases value with
  | manualAskAutomatedBid => decide
  | manualBidAutomatedAsk => decide
  | fastTrading => decide
  | manualBidAndAsk => decide
  | orderImbalance => decide
  | closedQuote => decide
  | nonfirmQuote => decide
  | openingQuoteAutomated => decide
  | regularTwosidedOpenQuoteAutomated => decide
  | manualBidAndAskNonfirm => decide
  | orderInflux => decide
  | automatedBidNoOfferOrAutomatedOfferNoBid => decide
  | noOpennoResume => decide
  | intradayAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Cond) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Cond × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Cond) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Cond) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Cond

/-- Rii: one byte code -/
def Rii.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43]

inductive Rii where
  | retailInterestNotApplicable -- Retail Interest Not Applicable
  | retailInterestOnBidQuote -- Retail Interest On Bid Quote
  | retailInterestOnAskQuote -- Retail Interest On Ask Quote
  | retailInterestOnBothBidAndAskQuote -- Retail Interest On Both Bid And Ask Quote
  | unlisted (byte : { byte : UInt8 // byte ∉ Rii.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Rii

def toByte : Rii → UInt8
  | .retailInterestNotApplicable => 0x20
  | .retailInterestOnBidQuote => 0x41
  | .retailInterestOnAskQuote => 0x42
  | .retailInterestOnBothBidAndAskQuote => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Rii :=
  if byte = 0x20 then .retailInterestNotApplicable
  else if byte = 0x41 then .retailInterestOnBidQuote
  else if byte = 0x42 then .retailInterestOnAskQuote
  else .retailInterestOnBothBidAndAskQuote

def ofByte (byte : UInt8) : Rii :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Rii) : ofByte value.toByte = value := by
  cases value with
  | retailInterestNotApplicable => decide
  | retailInterestOnBidQuote => decide
  | retailInterestOnAskQuote => decide
  | retailInterestOnBothBidAndAskQuote => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Rii) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Rii × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Rii) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Rii) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Rii

/-- Bbo Cond: one byte code -/
def BboCond.codes : List UInt8 :=
  [0x41, 0x42, 0x46, 0x48, 0x49, 0x4C, 0x4E, 0x4F, 0x52]

inductive BboCond where
  | manualAskAutomatedBid -- Manual Ask Automated Bid
  | manualBidAutomatedAsk -- Manual Bid Automated Ask
  | fastTrading -- Fast Trading
  | manualBidAndAsk -- Manual Bid And Ask
  | orderImbalance -- Order Imbalance
  | closedQuote -- Closed Quote
  | nonfirmQuote -- Nonfirm Quote
  | openingQuoteAutomated -- Opening Quote Automated
  | regularTwosidedOpenQuoteAutomated -- Regular Twosided Open Quote Automated
  | unlisted (byte : { byte : UInt8 // byte ∉ BboCond.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BboCond

def toByte : BboCond → UInt8
  | .manualAskAutomatedBid => 0x41
  | .manualBidAutomatedAsk => 0x42
  | .fastTrading => 0x46
  | .manualBidAndAsk => 0x48
  | .orderImbalance => 0x49
  | .closedQuote => 0x4C
  | .nonfirmQuote => 0x4E
  | .openingQuoteAutomated => 0x4F
  | .regularTwosidedOpenQuoteAutomated => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BboCond :=
  if byte = 0x41 then .manualAskAutomatedBid
  else if byte = 0x42 then .manualBidAutomatedAsk
  else if byte = 0x46 then .fastTrading
  else if byte = 0x48 then .manualBidAndAsk
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x4C then .closedQuote
  else if byte = 0x4E then .nonfirmQuote
  else if byte = 0x4F then .openingQuoteAutomated
  else .regularTwosidedOpenQuoteAutomated

def ofByte (byte : UInt8) : BboCond :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BboCond) : ofByte value.toByte = value := by
  cases value with
  | manualAskAutomatedBid => decide
  | manualBidAutomatedAsk => decide
  | fastTrading => decide
  | manualBidAndAsk => decide
  | orderImbalance => decide
  | closedQuote => decide
  | nonfirmQuote => decide
  | openingQuoteAutomated => decide
  | regularTwosidedOpenQuoteAutomated => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BboCond) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BboCond × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BboCond) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BboCond) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BboCond

/-- Bbo Indicator: one byte code -/
def BboIndicator.codes : List UInt8 :=
  [0x41, 0x42]

inductive BboIndicator where
  | noFinraBboChange -- No Finra Bbo Change
  | noFinraBboExists -- No Finra Bbo Exists
  | unlisted (byte : { byte : UInt8 // byte ∉ BboIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BboIndicator

def toByte : BboIndicator → UInt8
  | .noFinraBboChange => 0x41
  | .noFinraBboExists => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BboIndicator :=
  if byte = 0x41 then .noFinraBboChange
  else .noFinraBboExists

def ofByte (byte : UInt8) : BboIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BboIndicator) : ofByte value.toByte = value := by
  cases value with
  | noFinraBboChange => decide
  | noFinraBboExists => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BboIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BboIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BboIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BboIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BboIndicator

/-- Tt Exempt: one byte code -/
def TtExempt.codes : List UInt8 :=
  [0x58, 0x20]

inductive TtExempt where
  | rule611TradeThroughExempt -- Rule 611 Trade Through Exempt
  | notRule611TradeThroughExempt -- Not Rule 611 Trade Through Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ TtExempt.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TtExempt

def toByte : TtExempt → UInt8
  | .rule611TradeThroughExempt => 0x58
  | .notRule611TradeThroughExempt => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TtExempt :=
  if byte = 0x58 then .rule611TradeThroughExempt
  else .notRule611TradeThroughExempt

def ofByte (byte : UInt8) : TtExempt :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TtExempt) : ofByte value.toByte = value := by
  cases value with
  | rule611TradeThroughExempt => decide
  | notRule611TradeThroughExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TtExempt) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TtExempt × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TtExempt) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TtExempt) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TtExempt

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x58, 0x52]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | cross -- Cross
  | shortSale -- Short Sale
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .cross => 0x58
  | .shortSale => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x58 then .cross
  else .shortSale

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | cross => decide
  | shortSale => decide
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

/-- Cancel Type: one byte code -/
def CancelType.codes : List UInt8 :=
  [0x43, 0x45]

inductive CancelType where
  | cancel -- Cancel
  | error -- Error
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelType

def toByte : CancelType → UInt8
  | .cancel => 0x43
  | .error => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelType :=
  if byte = 0x43 then .cancel
  else .error

def ofByte (byte : UInt8) : CancelType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelType) : ofByte value.toByte = value := by
  cases value with
  | cancel => decide
  | error => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CancelType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelType

/-- Reversal: one byte code -/
def Reversal.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Reversal where
  | transactionRepresentsAReversal -- Transaction Represents A Reversal
  | transactionDoesNotRepresentAReversal -- Transaction Does Not Represent A Reversal
  | unlisted (byte : { byte : UInt8 // byte ∉ Reversal.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reversal

def toByte : Reversal → UInt8
  | .transactionRepresentsAReversal => 0x59
  | .transactionDoesNotRepresentAReversal => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reversal :=
  if byte = 0x59 then .transactionRepresentsAReversal
  else .transactionDoesNotRepresentAReversal

def ofByte (byte : UInt8) : Reversal :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reversal) : ofByte value.toByte = value := by
  cases value with
  | transactionRepresentsAReversal => decide
  | transactionDoesNotRepresentAReversal => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Reversal) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Reversal × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Reversal) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Reversal) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Reversal

/-- Action: one byte code -/
def Action.codes : List UInt8 :=
  [0x48, 0x51, 0x54, 0x50, 0x57, 0x45, 0x4F]

inductive Action where
  | tradingHalt -- Trading Halt
  | quotationResumptionIncludingRevokeEmergencyMarketAction -- Quotation Resumption Including Revoke Emergency Market Action
  | tradingResumption -- Trading Resumption
  | volatilityTradingPause -- Volatility Trading Pause
  | wipeoutQuote -- Wipeout Quote
  | emergencyMarketActionWipeoutAndRejectNewQuotes -- Emergency Market Action Wipeout And Reject New Quotes
  | clearOddLotQuotes -- Clear Odd Lot Quotes
  | unlisted (byte : { byte : UInt8 // byte ∉ Action.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Action

def toByte : Action → UInt8
  | .tradingHalt => 0x48
  | .quotationResumptionIncludingRevokeEmergencyMarketAction => 0x51
  | .tradingResumption => 0x54
  | .volatilityTradingPause => 0x50
  | .wipeoutQuote => 0x57
  | .emergencyMarketActionWipeoutAndRejectNewQuotes => 0x45
  | .clearOddLotQuotes => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Action :=
  if byte = 0x48 then .tradingHalt
  else if byte = 0x51 then .quotationResumptionIncludingRevokeEmergencyMarketAction
  else if byte = 0x54 then .tradingResumption
  else if byte = 0x50 then .volatilityTradingPause
  else if byte = 0x57 then .wipeoutQuote
  else if byte = 0x45 then .emergencyMarketActionWipeoutAndRejectNewQuotes
  else .clearOddLotQuotes

def ofByte (byte : UInt8) : Action :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Action) : ofByte value.toByte = value := by
  cases value with
  | tradingHalt => decide
  | quotationResumptionIncludingRevokeEmergencyMarketAction => decide
  | tradingResumption => decide
  | volatilityTradingPause => decide
  | wipeoutQuote => decide
  | emergencyMarketActionWipeoutAndRejectNewQuotes => decide
  | clearOddLotQuotes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Action) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Action × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Action) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Action) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Action

/-- Syntax Violation: one byte code -/
def SyntaxViolation.codes : List UInt8 :=
  [0x59, 0x4E]

inductive SyntaxViolation where
  | syntaxViolationPortWillDisconnect -- Syntax Violation— Port Will Disconnect
  | noSyntaxViolation -- No Syntax Violation
  | unlisted (byte : { byte : UInt8 // byte ∉ SyntaxViolation.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SyntaxViolation

def toByte : SyntaxViolation → UInt8
  | .syntaxViolationPortWillDisconnect => 0x59
  | .noSyntaxViolation => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SyntaxViolation :=
  if byte = 0x59 then .syntaxViolationPortWillDisconnect
  else .noSyntaxViolation

def ofByte (byte : UInt8) : SyntaxViolation :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SyntaxViolation) : ofByte value.toByte = value := by
  cases value with
  | syntaxViolationPortWillDisconnect => decide
  | noSyntaxViolation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SyntaxViolation) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SyntaxViolation × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SyntaxViolation) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SyntaxViolation) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SyntaxViolation

/-- Sip State: one byte code -/
def SipState.codes : List UInt8 :=
  [0x4E, 0x53, 0x45]

inductive SipState where
  | beforeStartOfDaySod -- Before Start Of Day Sod
  | afterStartOfDaySodBeforeEndOfDayEod -- After Start Of Day Sod Before End Of Day Eod
  | afterEndOfDayEod -- After End Of Day Eod
  | unlisted (byte : { byte : UInt8 // byte ∉ SipState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SipState

def toByte : SipState → UInt8
  | .beforeStartOfDaySod => 0x4E
  | .afterStartOfDaySodBeforeEndOfDayEod => 0x53
  | .afterEndOfDayEod => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SipState :=
  if byte = 0x4E then .beforeStartOfDaySod
  else if byte = 0x53 then .afterStartOfDaySodBeforeEndOfDayEod
  else .afterEndOfDayEod

def ofByte (byte : UInt8) : SipState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SipState) : ofByte value.toByte = value := by
  cases value with
  | beforeStartOfDaySod => decide
  | afterStartOfDaySodBeforeEndOfDayEod => decide
  | afterEndOfDayEod => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SipState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SipState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SipState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SipState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SipState

/-- Symbol State: one byte code -/
def SymbolState.codes : List UInt8 :=
  [0x48, 0x51, 0x54, 0x50]

inductive SymbolState where
  | tradingHalt -- Trading Halt
  | quotationOnly -- Quotation Only
  | trading -- Trading
  | volatilityTradingPause -- Volatility Trading Pause
  | unlisted (byte : { byte : UInt8 // byte ∉ SymbolState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SymbolState

def toByte : SymbolState → UInt8
  | .tradingHalt => 0x48
  | .quotationOnly => 0x51
  | .trading => 0x54
  | .volatilityTradingPause => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SymbolState :=
  if byte = 0x48 then .tradingHalt
  else if byte = 0x51 then .quotationOnly
  else if byte = 0x54 then .trading
  else .volatilityTradingPause

def ofByte (byte : UInt8) : SymbolState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SymbolState) : ofByte value.toByte = value := by
  cases value with
  | tradingHalt => decide
  | quotationOnly => decide
  | trading => decide
  | volatilityTradingPause => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SymbolState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SymbolState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SymbolState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SymbolState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SymbolState

/-- Protected Exchange Quote Message Shortform Message: 41 bytes -/
structure ProtectedExchangeQuoteMessageShortformMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolShort : Alpha 5
  bidShort : BitVec 16
  bidSizeShort : BitVec 16
  askShort : BitVec 16
  askSizeShort : BitVec 16
  cond : Cond
  rii : Rii
  deriving DecidableEq, Repr

namespace ProtectedExchangeQuoteMessageShortformMessage

def encode (message : ProtectedExchangeQuoteMessageShortformMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolShort
    ++ (encodeUInt 2 message.bidShort
    ++ (encodeUInt 2 message.bidSizeShort
    ++ (encodeUInt 2 message.askShort
    ++ (encodeUInt 2 message.askSizeShort
    ++ (Cond.encode message.cond
    ++ (Rii.encode message.rii))))))))))

def decode (bytes : List UInt8) : Option (ProtectedExchangeQuoteMessageShortformMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolShort, bytes) ← Alpha.decode 5 bytes
  let (bidShort, bytes) ← decodeUInt 2 bytes
  let (bidSizeShort, bytes) ← decodeUInt 2 bytes
  let (askShort, bytes) ← decodeUInt 2 bytes
  let (askSizeShort, bytes) ← decodeUInt 2 bytes
  let (cond, bytes) ← Cond.decode bytes
  let (rii, bytes) ← Rii.decode bytes
  pure ({ orig, timestamp1, feedSequence, partToken, symbolShort, bidShort, bidSizeShort, askShort, askSizeShort, cond, rii }, bytes)

@[simp] theorem encode_length (message : ProtectedExchangeQuoteMessageShortformMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Cond.encode_length, Rii.encode_length]

theorem encode_length_pos (message : ProtectedExchangeQuoteMessageShortformMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProtectedExchangeQuoteMessageShortformMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Cond.decode_encode, some_bind]
  dsimp only
  rw [Rii.decode_encode, some_bind]
  rfl

end ProtectedExchangeQuoteMessageShortformMessage

/-- Protected Exchange Quote Message Longform Message: 63 bytes -/
structure ProtectedExchangeQuoteMessageLongformMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolLong : Alpha 11
  bidLong : BitVec 64
  bidSizeLong : BitVec 32
  askLong : BitVec 64
  askSizeLong : BitVec 32
  cond : Cond
  rii : Rii
  deriving DecidableEq, Repr

namespace ProtectedExchangeQuoteMessageLongformMessage

def encode (message : ProtectedExchangeQuoteMessageLongformMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 8 message.bidLong
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 8 message.askLong
    ++ (encodeUInt 4 message.askSizeLong
    ++ (Cond.encode message.cond
    ++ (Rii.encode message.rii))))))))))

def decode (bytes : List UInt8) : Option (ProtectedExchangeQuoteMessageLongformMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (bidLong, bytes) ← decodeUInt 8 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (askLong, bytes) ← decodeUInt 8 bytes
  let (askSizeLong, bytes) ← decodeUInt 4 bytes
  let (cond, bytes) ← Cond.decode bytes
  let (rii, bytes) ← Rii.decode bytes
  pure ({ orig, timestamp1, feedSequence, partToken, symbolLong, bidLong, bidSizeLong, askLong, askSizeLong, cond, rii }, bytes)

@[simp] theorem encode_length (message : ProtectedExchangeQuoteMessageLongformMessage) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Cond.encode_length, Rii.encode_length]

theorem encode_length_pos (message : ProtectedExchangeQuoteMessageLongformMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProtectedExchangeQuoteMessageLongformMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Cond.decode_encode, some_bind]
  dsimp only
  rw [Rii.decode_encode, some_bind]
  rfl

end ProtectedExchangeQuoteMessageLongformMessage

/-- Odd Lot Bid Short Form Attachment: 4 bytes -/
structure OddLotBidShortFormAttachment where
  olPriceShort : BitVec 16
  olSize : BitVec 16
  deriving DecidableEq, Repr

namespace OddLotBidShortFormAttachment

def encode (message : OddLotBidShortFormAttachment) : List UInt8 :=
  encodeUInt 2 message.olPriceShort
    ++ (encodeUInt 2 message.olSize)

def decode (bytes : List UInt8) : Option (OddLotBidShortFormAttachment × List UInt8) := do
  let (olPriceShort, bytes) ← decodeUInt 2 bytes
  let (olSize, bytes) ← decodeUInt 2 bytes
  pure ({ olPriceShort, olSize }, bytes)

@[simp] theorem encode_length (message : OddLotBidShortFormAttachment) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OddLotBidShortFormAttachment) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OddLotBidShortFormAttachment) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OddLotBidShortFormAttachment

/-- Odd Lot Ask Short Form Attachment: 4 bytes -/
structure OddLotAskShortFormAttachment where
  olPriceShort : BitVec 16
  olSize : BitVec 16
  deriving DecidableEq, Repr

namespace OddLotAskShortFormAttachment

def encode (message : OddLotAskShortFormAttachment) : List UInt8 :=
  encodeUInt 2 message.olPriceShort
    ++ (encodeUInt 2 message.olSize)

def decode (bytes : List UInt8) : Option (OddLotAskShortFormAttachment × List UInt8) := do
  let (olPriceShort, bytes) ← decodeUInt 2 bytes
  let (olSize, bytes) ← decodeUInt 2 bytes
  pure ({ olPriceShort, olSize }, bytes)

@[simp] theorem encode_length (message : OddLotAskShortFormAttachment) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OddLotAskShortFormAttachment) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OddLotAskShortFormAttachment) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OddLotAskShortFormAttachment

/-- Exchange Odd Lot Quote Message Short Form Message -/
structure ExchangeOddLotQuoteMessageShortFormMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolShort : Alpha 5
  oddLotBidShortFormAttachment : Bounded 2 OddLotBidShortFormAttachment
  oddLotAskShortFormAttachment : Bounded 2 OddLotAskShortFormAttachment
  deriving DecidableEq, Repr

namespace ExchangeOddLotQuoteMessageShortFormMessage

def encode (message : ExchangeOddLotQuoteMessageShortFormMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolShort
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.oddLotBidShortFormAttachment.val.length)
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.oddLotAskShortFormAttachment.val.length)
    ++ (encodeMany OddLotBidShortFormAttachment.encode message.oddLotBidShortFormAttachment.val
    ++ (encodeMany OddLotAskShortFormAttachment.encode message.oddLotAskShortFormAttachment.val))))))))

def decode (bytes : List UInt8) : Option (ExchangeOddLotQuoteMessageShortFormMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolShort, bytes) ← Alpha.decode 5 bytes
  let (olBidLevelCount, bytes) ← decodeUInt 2 bytes
  let (olAskLevelCount, bytes) ← decodeUInt 2 bytes
  let (oddLotBidShortFormAttachment_, bytes) ← decodeMany OddLotBidShortFormAttachment.decode olBidLevelCount.toNat bytes
  let (oddLotAskShortFormAttachment_, bytes) ← decodeMany OddLotAskShortFormAttachment.decode olAskLevelCount.toNat bytes
  if fits_oddLotBidShortFormAttachment : oddLotBidShortFormAttachment_.length < 256 ^ 2 then
    if fits_oddLotAskShortFormAttachment : oddLotAskShortFormAttachment_.length < 256 ^ 2 then
      pure ({ orig, timestamp1, feedSequence, partToken, symbolShort, oddLotBidShortFormAttachment := ⟨oddLotBidShortFormAttachment_, fits_oddLotBidShortFormAttachment⟩, oddLotAskShortFormAttachment := ⟨oddLotAskShortFormAttachment_, fits_oddLotAskShortFormAttachment⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : ExchangeOddLotQuoteMessageShortFormMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExchangeOddLotQuoteMessageShortFormMessage) : (encode message).length ≤ 524315 := by
  have bound_oddLotBidShortFormAttachment := message.oddLotBidShortFormAttachment.length_lt
  have bound_oddLotAskShortFormAttachment := message.oddLotAskShortFormAttachment.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const OddLotBidShortFormAttachment.encode 4 OddLotBidShortFormAttachment.encode_length, encodeMany_length_const OddLotAskShortFormAttachment.encode 4 OddLotAskShortFormAttachment.encode_length]
  omega

@[simp] theorem decode_encode (message : ExchangeOddLotQuoteMessageShortFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeMany_bounded 2 OddLotBidShortFormAttachment.encode OddLotBidShortFormAttachment.decode OddLotBidShortFormAttachment.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 OddLotAskShortFormAttachment.encode OddLotAskShortFormAttachment.decode OddLotAskShortFormAttachment.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.oddLotBidShortFormAttachment.length_lt, dite_eq_left message.oddLotAskShortFormAttachment.length_lt]
  rfl

end ExchangeOddLotQuoteMessageShortFormMessage

/-- Odd Lot Bid Long Form Attachment: 10 bytes -/
structure OddLotBidLongFormAttachment where
  olPriceLong : BitVec 64
  olSize : BitVec 16
  deriving DecidableEq, Repr

namespace OddLotBidLongFormAttachment

def encode (message : OddLotBidLongFormAttachment) : List UInt8 :=
  encodeUInt 8 message.olPriceLong
    ++ (encodeUInt 2 message.olSize)

def decode (bytes : List UInt8) : Option (OddLotBidLongFormAttachment × List UInt8) := do
  let (olPriceLong, bytes) ← decodeUInt 8 bytes
  let (olSize, bytes) ← decodeUInt 2 bytes
  pure ({ olPriceLong, olSize }, bytes)

@[simp] theorem encode_length (message : OddLotBidLongFormAttachment) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OddLotBidLongFormAttachment) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OddLotBidLongFormAttachment) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OddLotBidLongFormAttachment

/-- Odd Lot Ask Long Form Attachment: 10 bytes -/
structure OddLotAskLongFormAttachment where
  olPriceLong : BitVec 64
  olSize : BitVec 16
  deriving DecidableEq, Repr

namespace OddLotAskLongFormAttachment

def encode (message : OddLotAskLongFormAttachment) : List UInt8 :=
  encodeUInt 8 message.olPriceLong
    ++ (encodeUInt 2 message.olSize)

def decode (bytes : List UInt8) : Option (OddLotAskLongFormAttachment × List UInt8) := do
  let (olPriceLong, bytes) ← decodeUInt 8 bytes
  let (olSize, bytes) ← decodeUInt 2 bytes
  pure ({ olPriceLong, olSize }, bytes)

@[simp] theorem encode_length (message : OddLotAskLongFormAttachment) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OddLotAskLongFormAttachment) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OddLotAskLongFormAttachment) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OddLotAskLongFormAttachment

/-- Exchange Odd Lot Quote Message Long Form Message -/
structure ExchangeOddLotQuoteMessageLongFormMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolLong : Alpha 11
  oddLotBidLongFormAttachment : Bounded 2 OddLotBidLongFormAttachment
  oddLotAskLongFormAttachment : Bounded 2 OddLotAskLongFormAttachment
  deriving DecidableEq, Repr

namespace ExchangeOddLotQuoteMessageLongFormMessage

def encode (message : ExchangeOddLotQuoteMessageLongFormMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.oddLotBidLongFormAttachment.val.length)
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.oddLotAskLongFormAttachment.val.length)
    ++ (encodeMany OddLotBidLongFormAttachment.encode message.oddLotBidLongFormAttachment.val
    ++ (encodeMany OddLotAskLongFormAttachment.encode message.oddLotAskLongFormAttachment.val))))))))

def decode (bytes : List UInt8) : Option (ExchangeOddLotQuoteMessageLongFormMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (olBidLevelCount, bytes) ← decodeUInt 2 bytes
  let (olAskLevelCount, bytes) ← decodeUInt 2 bytes
  let (oddLotBidLongFormAttachment_, bytes) ← decodeMany OddLotBidLongFormAttachment.decode olBidLevelCount.toNat bytes
  let (oddLotAskLongFormAttachment_, bytes) ← decodeMany OddLotAskLongFormAttachment.decode olAskLevelCount.toNat bytes
  if fits_oddLotBidLongFormAttachment : oddLotBidLongFormAttachment_.length < 256 ^ 2 then
    if fits_oddLotAskLongFormAttachment : oddLotAskLongFormAttachment_.length < 256 ^ 2 then
      pure ({ orig, timestamp1, feedSequence, partToken, symbolLong, oddLotBidLongFormAttachment := ⟨oddLotBidLongFormAttachment_, fits_oddLotBidLongFormAttachment⟩, oddLotAskLongFormAttachment := ⟨oddLotAskLongFormAttachment_, fits_oddLotAskLongFormAttachment⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : ExchangeOddLotQuoteMessageLongFormMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExchangeOddLotQuoteMessageLongFormMessage) : (encode message).length ≤ 1310741 := by
  have bound_oddLotBidLongFormAttachment := message.oddLotBidLongFormAttachment.length_lt
  have bound_oddLotAskLongFormAttachment := message.oddLotAskLongFormAttachment.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const OddLotBidLongFormAttachment.encode 10 OddLotBidLongFormAttachment.encode_length, encodeMany_length_const OddLotAskLongFormAttachment.encode 10 OddLotAskLongFormAttachment.encode_length]
  omega

@[simp] theorem decode_encode (message : ExchangeOddLotQuoteMessageLongFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeMany_bounded 2 OddLotBidLongFormAttachment.encode OddLotBidLongFormAttachment.decode OddLotBidLongFormAttachment.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 OddLotAskLongFormAttachment.encode OddLotAskLongFormAttachment.decode OddLotAskLongFormAttachment.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.oddLotBidLongFormAttachment.length_lt, dite_eq_left message.oddLotAskLongFormAttachment.length_lt]
  rfl

end ExchangeOddLotQuoteMessageLongFormMessage

/-- Exchange Combined Quote Message Short Form Message -/
structure ExchangeCombinedQuoteMessageShortFormMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolShort : Alpha 5
  bidShort : BitVec 16
  bidSizeShort : BitVec 16
  askShort : BitVec 16
  askSizeShort : BitVec 16
  cond : Cond
  rii : Rii
  oddLotBidShortFormAttachment : Bounded 2 OddLotBidShortFormAttachment
  oddLotAskShortFormAttachment : Bounded 2 OddLotAskShortFormAttachment
  deriving DecidableEq, Repr

namespace ExchangeCombinedQuoteMessageShortFormMessage

def encode (message : ExchangeCombinedQuoteMessageShortFormMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolShort
    ++ (encodeUInt 2 message.bidShort
    ++ (encodeUInt 2 message.bidSizeShort
    ++ (encodeUInt 2 message.askShort
    ++ (encodeUInt 2 message.askSizeShort
    ++ (Cond.encode message.cond
    ++ (Rii.encode message.rii
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.oddLotBidShortFormAttachment.val.length)
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.oddLotAskShortFormAttachment.val.length)
    ++ (encodeMany OddLotBidShortFormAttachment.encode message.oddLotBidShortFormAttachment.val
    ++ (encodeMany OddLotAskShortFormAttachment.encode message.oddLotAskShortFormAttachment.val))))))))))))))

def decode (bytes : List UInt8) : Option (ExchangeCombinedQuoteMessageShortFormMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolShort, bytes) ← Alpha.decode 5 bytes
  let (bidShort, bytes) ← decodeUInt 2 bytes
  let (bidSizeShort, bytes) ← decodeUInt 2 bytes
  let (askShort, bytes) ← decodeUInt 2 bytes
  let (askSizeShort, bytes) ← decodeUInt 2 bytes
  let (cond, bytes) ← Cond.decode bytes
  let (rii, bytes) ← Rii.decode bytes
  let (olBidLevelCount, bytes) ← decodeUInt 2 bytes
  let (olAskLevelCount, bytes) ← decodeUInt 2 bytes
  let (oddLotBidShortFormAttachment_, bytes) ← decodeMany OddLotBidShortFormAttachment.decode olBidLevelCount.toNat bytes
  let (oddLotAskShortFormAttachment_, bytes) ← decodeMany OddLotAskShortFormAttachment.decode olAskLevelCount.toNat bytes
  if fits_oddLotBidShortFormAttachment : oddLotBidShortFormAttachment_.length < 256 ^ 2 then
    if fits_oddLotAskShortFormAttachment : oddLotAskShortFormAttachment_.length < 256 ^ 2 then
      pure ({ orig, timestamp1, feedSequence, partToken, symbolShort, bidShort, bidSizeShort, askShort, askSizeShort, cond, rii, oddLotBidShortFormAttachment := ⟨oddLotBidShortFormAttachment_, fits_oddLotBidShortFormAttachment⟩, oddLotAskShortFormAttachment := ⟨oddLotAskShortFormAttachment_, fits_oddLotAskShortFormAttachment⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : ExchangeCombinedQuoteMessageShortFormMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExchangeCombinedQuoteMessageShortFormMessage) : (encode message).length ≤ 524325 := by
  have bound_oddLotBidShortFormAttachment := message.oddLotBidShortFormAttachment.length_lt
  have bound_oddLotAskShortFormAttachment := message.oddLotAskShortFormAttachment.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, Cond.encode_length, Rii.encode_length, encodeMany_length_const OddLotBidShortFormAttachment.encode 4 OddLotBidShortFormAttachment.encode_length, encodeMany_length_const OddLotAskShortFormAttachment.encode 4 OddLotAskShortFormAttachment.encode_length]
  omega

@[simp] theorem decode_encode (message : ExchangeCombinedQuoteMessageShortFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Cond.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Rii.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 2 OddLotBidShortFormAttachment.encode OddLotBidShortFormAttachment.decode OddLotBidShortFormAttachment.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 OddLotAskShortFormAttachment.encode OddLotAskShortFormAttachment.decode OddLotAskShortFormAttachment.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.oddLotBidShortFormAttachment.length_lt, dite_eq_left message.oddLotAskShortFormAttachment.length_lt]
  rfl

end ExchangeCombinedQuoteMessageShortFormMessage

/-- Exchange Combined Quote Message Long Form Message -/
structure ExchangeCombinedQuoteMessageLongFormMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolLong : Alpha 11
  bidLong : BitVec 64
  bidSizeLong : BitVec 32
  askLong : BitVec 64
  askSizeLong : BitVec 32
  cond : Cond
  rii : Rii
  oddLotBidLongFormAttachment : Bounded 2 OddLotBidLongFormAttachment
  oddLotAskLongFormAttachment : Bounded 2 OddLotAskLongFormAttachment
  deriving DecidableEq, Repr

namespace ExchangeCombinedQuoteMessageLongFormMessage

def encode (message : ExchangeCombinedQuoteMessageLongFormMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 8 message.bidLong
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 8 message.askLong
    ++ (encodeUInt 4 message.askSizeLong
    ++ (Cond.encode message.cond
    ++ (Rii.encode message.rii
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.oddLotBidLongFormAttachment.val.length)
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.oddLotAskLongFormAttachment.val.length)
    ++ (encodeMany OddLotBidLongFormAttachment.encode message.oddLotBidLongFormAttachment.val
    ++ (encodeMany OddLotAskLongFormAttachment.encode message.oddLotAskLongFormAttachment.val))))))))))))))

def decode (bytes : List UInt8) : Option (ExchangeCombinedQuoteMessageLongFormMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (bidLong, bytes) ← decodeUInt 8 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (askLong, bytes) ← decodeUInt 8 bytes
  let (askSizeLong, bytes) ← decodeUInt 4 bytes
  let (cond, bytes) ← Cond.decode bytes
  let (rii, bytes) ← Rii.decode bytes
  let (olBidLevelCount, bytes) ← decodeUInt 2 bytes
  let (olAskLevelCount, bytes) ← decodeUInt 2 bytes
  let (oddLotBidLongFormAttachment_, bytes) ← decodeMany OddLotBidLongFormAttachment.decode olBidLevelCount.toNat bytes
  let (oddLotAskLongFormAttachment_, bytes) ← decodeMany OddLotAskLongFormAttachment.decode olAskLevelCount.toNat bytes
  if fits_oddLotBidLongFormAttachment : oddLotBidLongFormAttachment_.length < 256 ^ 2 then
    if fits_oddLotAskLongFormAttachment : oddLotAskLongFormAttachment_.length < 256 ^ 2 then
      pure ({ orig, timestamp1, feedSequence, partToken, symbolLong, bidLong, bidSizeLong, askLong, askSizeLong, cond, rii, oddLotBidLongFormAttachment := ⟨oddLotBidLongFormAttachment_, fits_oddLotBidLongFormAttachment⟩, oddLotAskLongFormAttachment := ⟨oddLotAskLongFormAttachment_, fits_oddLotAskLongFormAttachment⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : ExchangeCombinedQuoteMessageLongFormMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExchangeCombinedQuoteMessageLongFormMessage) : (encode message).length ≤ 1310767 := by
  have bound_oddLotBidLongFormAttachment := message.oddLotBidLongFormAttachment.length_lt
  have bound_oddLotAskLongFormAttachment := message.oddLotAskLongFormAttachment.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, Cond.encode_length, Rii.encode_length, encodeMany_length_const OddLotBidLongFormAttachment.encode 10 OddLotBidLongFormAttachment.encode_length, encodeMany_length_const OddLotAskLongFormAttachment.encode 10 OddLotAskLongFormAttachment.encode_length]
  omega

@[simp] theorem decode_encode (message : ExchangeCombinedQuoteMessageLongFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Cond.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Rii.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 2 OddLotBidLongFormAttachment.encode OddLotBidLongFormAttachment.decode OddLotBidLongFormAttachment.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 OddLotAskLongFormAttachment.encode OddLotAskLongFormAttachment.decode OddLotAskLongFormAttachment.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.oddLotBidLongFormAttachment.length_lt, dite_eq_left message.oddLotAskLongFormAttachment.length_lt]
  rfl

end ExchangeCombinedQuoteMessageLongFormMessage

/-- Finra Protected Quote Message With Bbo Info Message: 107 bytes -/
structure FinraProtectedQuoteMessageWithBboInfoMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  timestamp2 : BitVec 64
  symbolLong : Alpha 11
  bidLong : BitVec 64
  bidSizeLong : BitVec 32
  askLong : BitVec 64
  askSizeLong : BitVec 32
  cond : Cond
  mpid : Alpha 4
  bboBid : BitVec 64
  bboBidSize : BitVec 32
  bboBidMpid : Alpha 4
  bboAsk : BitVec 64
  bboAskSize : BitVec 32
  bboAskMpid : Alpha 4
  bboCond : BboCond
  deriving DecidableEq, Repr

namespace FinraProtectedQuoteMessageWithBboInfoMessage

def encode (message : FinraProtectedQuoteMessageWithBboInfoMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (encodeUInt 8 message.timestamp2
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 8 message.bidLong
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 8 message.askLong
    ++ (encodeUInt 4 message.askSizeLong
    ++ (Cond.encode message.cond
    ++ (Alpha.encode message.mpid
    ++ (encodeUInt 8 message.bboBid
    ++ (encodeUInt 4 message.bboBidSize
    ++ (Alpha.encode message.bboBidMpid
    ++ (encodeUInt 8 message.bboAsk
    ++ (encodeUInt 4 message.bboAskSize
    ++ (Alpha.encode message.bboAskMpid
    ++ (BboCond.encode message.bboCond))))))))))))))))))

def decode (bytes : List UInt8) : Option (FinraProtectedQuoteMessageWithBboInfoMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (timestamp2, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (bidLong, bytes) ← decodeUInt 8 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (askLong, bytes) ← decodeUInt 8 bytes
  let (askSizeLong, bytes) ← decodeUInt 4 bytes
  let (cond, bytes) ← Cond.decode bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (bboBid, bytes) ← decodeUInt 8 bytes
  let (bboBidSize, bytes) ← decodeUInt 4 bytes
  let (bboBidMpid, bytes) ← Alpha.decode 4 bytes
  let (bboAsk, bytes) ← decodeUInt 8 bytes
  let (bboAskSize, bytes) ← decodeUInt 4 bytes
  let (bboAskMpid, bytes) ← Alpha.decode 4 bytes
  let (bboCond, bytes) ← BboCond.decode bytes
  pure ({ orig, timestamp1, feedSequence, partToken, timestamp2, symbolLong, bidLong, bidSizeLong, askLong, askSizeLong, cond, mpid, bboBid, bboBidSize, bboBidMpid, bboAsk, bboAskSize, bboAskMpid, bboCond }, bytes)

@[simp] theorem encode_length (message : FinraProtectedQuoteMessageWithBboInfoMessage) : (encode message).length = 107 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Cond.encode_length, BboCond.encode_length]

theorem encode_length_pos (message : FinraProtectedQuoteMessageWithBboInfoMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FinraProtectedQuoteMessageWithBboInfoMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Cond.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [BboCond.decode_encode, some_bind]
  rfl

end FinraProtectedQuoteMessageWithBboInfoMessage

/-- Finra Protected Quote Message Without Bbo Info Message: 75 bytes -/
structure FinraProtectedQuoteMessageWithoutBboInfoMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  timestamp2 : BitVec 64
  symbolLong : Alpha 11
  bidLong : BitVec 64
  bidSizeLong : BitVec 32
  askLong : BitVec 64
  askSizeLong : BitVec 32
  cond : Cond
  mpid : Alpha 4
  bboIndicator : BboIndicator
  deriving DecidableEq, Repr

namespace FinraProtectedQuoteMessageWithoutBboInfoMessage

def encode (message : FinraProtectedQuoteMessageWithoutBboInfoMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (encodeUInt 8 message.timestamp2
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 8 message.bidLong
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 8 message.askLong
    ++ (encodeUInt 4 message.askSizeLong
    ++ (Cond.encode message.cond
    ++ (Alpha.encode message.mpid
    ++ (BboIndicator.encode message.bboIndicator))))))))))))

def decode (bytes : List UInt8) : Option (FinraProtectedQuoteMessageWithoutBboInfoMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (timestamp2, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (bidLong, bytes) ← decodeUInt 8 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (askLong, bytes) ← decodeUInt 8 bytes
  let (askSizeLong, bytes) ← decodeUInt 4 bytes
  let (cond, bytes) ← Cond.decode bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (bboIndicator, bytes) ← BboIndicator.decode bytes
  pure ({ orig, timestamp1, feedSequence, partToken, timestamp2, symbolLong, bidLong, bidSizeLong, askLong, askSizeLong, cond, mpid, bboIndicator }, bytes)

@[simp] theorem encode_length (message : FinraProtectedQuoteMessageWithoutBboInfoMessage) : (encode message).length = 75 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Cond.encode_length, BboIndicator.encode_length]

theorem encode_length_pos (message : FinraProtectedQuoteMessageWithoutBboInfoMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FinraProtectedQuoteMessageWithoutBboInfoMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Cond.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [BboIndicator.decode_encode, some_bind]
  rfl

end FinraProtectedQuoteMessageWithoutBboInfoMessage

/-- Odd Lot Bid Adf Form Attachment: 14 bytes -/
structure OddLotBidAdfFormAttachment where
  olPriceLong : BitVec 64
  olSize : BitVec 16
  mpid : Alpha 4
  deriving DecidableEq, Repr

namespace OddLotBidAdfFormAttachment

def encode (message : OddLotBidAdfFormAttachment) : List UInt8 :=
  encodeUInt 8 message.olPriceLong
    ++ (encodeUInt 2 message.olSize
    ++ (Alpha.encode message.mpid))

def decode (bytes : List UInt8) : Option (OddLotBidAdfFormAttachment × List UInt8) := do
  let (olPriceLong, bytes) ← decodeUInt 8 bytes
  let (olSize, bytes) ← decodeUInt 2 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  pure ({ olPriceLong, olSize, mpid }, bytes)

@[simp] theorem encode_length (message : OddLotBidAdfFormAttachment) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OddLotBidAdfFormAttachment) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OddLotBidAdfFormAttachment) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OddLotBidAdfFormAttachment

/-- Odd Lot Ask Adf Form Attachment: 14 bytes -/
structure OddLotAskAdfFormAttachment where
  olPriceLong : BitVec 64
  olSize : BitVec 16
  mpid : Alpha 4
  deriving DecidableEq, Repr

namespace OddLotAskAdfFormAttachment

def encode (message : OddLotAskAdfFormAttachment) : List UInt8 :=
  encodeUInt 8 message.olPriceLong
    ++ (encodeUInt 2 message.olSize
    ++ (Alpha.encode message.mpid))

def decode (bytes : List UInt8) : Option (OddLotAskAdfFormAttachment × List UInt8) := do
  let (olPriceLong, bytes) ← decodeUInt 8 bytes
  let (olSize, bytes) ← decodeUInt 2 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  pure ({ olPriceLong, olSize, mpid }, bytes)

@[simp] theorem encode_length (message : OddLotAskAdfFormAttachment) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OddLotAskAdfFormAttachment) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OddLotAskAdfFormAttachment) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OddLotAskAdfFormAttachment

/-- Finra Adf Odd Lot Quotation Message -/
structure FinraAdfOddLotQuotationMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  timestamp2 : BitVec 64
  symbolLong : Alpha 11
  oddLotBidAdfFormAttachment : Bounded 2 OddLotBidAdfFormAttachment
  oddLotAskAdfFormAttachment : Bounded 2 OddLotAskAdfFormAttachment
  deriving DecidableEq, Repr

namespace FinraAdfOddLotQuotationMessage

def encode (message : FinraAdfOddLotQuotationMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (encodeUInt 8 message.timestamp2
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.oddLotBidAdfFormAttachment.val.length)
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.oddLotAskAdfFormAttachment.val.length)
    ++ (encodeMany OddLotBidAdfFormAttachment.encode message.oddLotBidAdfFormAttachment.val
    ++ (encodeMany OddLotAskAdfFormAttachment.encode message.oddLotAskAdfFormAttachment.val)))))))))

def decode (bytes : List UInt8) : Option (FinraAdfOddLotQuotationMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (timestamp2, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (olBidLevelCount, bytes) ← decodeUInt 2 bytes
  let (olAskLevelCount, bytes) ← decodeUInt 2 bytes
  let (oddLotBidAdfFormAttachment_, bytes) ← decodeMany OddLotBidAdfFormAttachment.decode olBidLevelCount.toNat bytes
  let (oddLotAskAdfFormAttachment_, bytes) ← decodeMany OddLotAskAdfFormAttachment.decode olAskLevelCount.toNat bytes
  if fits_oddLotBidAdfFormAttachment : oddLotBidAdfFormAttachment_.length < 256 ^ 2 then
    if fits_oddLotAskAdfFormAttachment : oddLotAskAdfFormAttachment_.length < 256 ^ 2 then
      pure ({ orig, timestamp1, feedSequence, partToken, timestamp2, symbolLong, oddLotBidAdfFormAttachment := ⟨oddLotBidAdfFormAttachment_, fits_oddLotBidAdfFormAttachment⟩, oddLotAskAdfFormAttachment := ⟨oddLotAskAdfFormAttachment_, fits_oddLotAskAdfFormAttachment⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : FinraAdfOddLotQuotationMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FinraAdfOddLotQuotationMessage) : (encode message).length ≤ 1835029 := by
  have bound_oddLotBidAdfFormAttachment := message.oddLotBidAdfFormAttachment.length_lt
  have bound_oddLotAskAdfFormAttachment := message.oddLotAskAdfFormAttachment.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const OddLotBidAdfFormAttachment.encode 14 OddLotBidAdfFormAttachment.encode_length, encodeMany_length_const OddLotAskAdfFormAttachment.encode 14 OddLotAskAdfFormAttachment.encode_length]
  omega

@[simp] theorem decode_encode (message : FinraAdfOddLotQuotationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 2 OddLotBidAdfFormAttachment.encode OddLotBidAdfFormAttachment.decode OddLotBidAdfFormAttachment.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 OddLotAskAdfFormAttachment.encode OddLotAskAdfFormAttachment.decode OddLotAskAdfFormAttachment.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.oddLotBidAdfFormAttachment.length_lt, dite_eq_left message.oddLotAskAdfFormAttachment.length_lt]
  rfl

end FinraAdfOddLotQuotationMessage

/-- Finra Adf Combined Quote Message With Bbo -/
structure FinraAdfCombinedQuoteMessageWithBbo where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  timestamp2 : BitVec 64
  symbolLong : Alpha 11
  bidLong : BitVec 64
  bidSizeLong : BitVec 32
  askLong : BitVec 64
  askSizeLong : BitVec 32
  cond : Cond
  mpid : Alpha 4
  rii : Rii
  bboBidPrice : BitVec 64
  bboBidSize : BitVec 32
  bboBidMpid : Alpha 4
  bboAskPrice : BitVec 64
  bboAskSize : BitVec 32
  bboAskMpid : Alpha 4
  bboCond : BboCond
  oddLotBidAdfFormAttachment : Bounded 2 OddLotBidAdfFormAttachment
  oddLotAskAdfFormAttachment : Bounded 2 OddLotAskAdfFormAttachment
  deriving DecidableEq, Repr

namespace FinraAdfCombinedQuoteMessageWithBbo

def encode (message : FinraAdfCombinedQuoteMessageWithBbo) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (encodeUInt 8 message.timestamp2
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 8 message.bidLong
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 8 message.askLong
    ++ (encodeUInt 4 message.askSizeLong
    ++ (Cond.encode message.cond
    ++ (Alpha.encode message.mpid
    ++ (Rii.encode message.rii
    ++ (encodeUInt 8 message.bboBidPrice
    ++ (encodeUInt 4 message.bboBidSize
    ++ (Alpha.encode message.bboBidMpid
    ++ (encodeUInt 8 message.bboAskPrice
    ++ (encodeUInt 4 message.bboAskSize
    ++ (Alpha.encode message.bboAskMpid
    ++ (BboCond.encode message.bboCond
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.oddLotBidAdfFormAttachment.val.length)
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.oddLotAskAdfFormAttachment.val.length)
    ++ (encodeMany OddLotBidAdfFormAttachment.encode message.oddLotBidAdfFormAttachment.val
    ++ (encodeMany OddLotAskAdfFormAttachment.encode message.oddLotAskAdfFormAttachment.val)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (FinraAdfCombinedQuoteMessageWithBbo × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (timestamp2, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (bidLong, bytes) ← decodeUInt 8 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (askLong, bytes) ← decodeUInt 8 bytes
  let (askSizeLong, bytes) ← decodeUInt 4 bytes
  let (cond, bytes) ← Cond.decode bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (rii, bytes) ← Rii.decode bytes
  let (bboBidPrice, bytes) ← decodeUInt 8 bytes
  let (bboBidSize, bytes) ← decodeUInt 4 bytes
  let (bboBidMpid, bytes) ← Alpha.decode 4 bytes
  let (bboAskPrice, bytes) ← decodeUInt 8 bytes
  let (bboAskSize, bytes) ← decodeUInt 4 bytes
  let (bboAskMpid, bytes) ← Alpha.decode 4 bytes
  let (bboCond, bytes) ← BboCond.decode bytes
  let (olBidLevelCount, bytes) ← decodeUInt 2 bytes
  let (olAskLevelCount, bytes) ← decodeUInt 2 bytes
  let (oddLotBidAdfFormAttachment_, bytes) ← decodeMany OddLotBidAdfFormAttachment.decode olBidLevelCount.toNat bytes
  let (oddLotAskAdfFormAttachment_, bytes) ← decodeMany OddLotAskAdfFormAttachment.decode olAskLevelCount.toNat bytes
  if fits_oddLotBidAdfFormAttachment : oddLotBidAdfFormAttachment_.length < 256 ^ 2 then
    if fits_oddLotAskAdfFormAttachment : oddLotAskAdfFormAttachment_.length < 256 ^ 2 then
      pure ({ orig, timestamp1, feedSequence, partToken, timestamp2, symbolLong, bidLong, bidSizeLong, askLong, askSizeLong, cond, mpid, rii, bboBidPrice, bboBidSize, bboBidMpid, bboAskPrice, bboAskSize, bboAskMpid, bboCond, oddLotBidAdfFormAttachment := ⟨oddLotBidAdfFormAttachment_, fits_oddLotBidAdfFormAttachment⟩, oddLotAskAdfFormAttachment := ⟨oddLotAskAdfFormAttachment_, fits_oddLotAskAdfFormAttachment⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : FinraAdfCombinedQuoteMessageWithBbo) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FinraAdfCombinedQuoteMessageWithBbo) : (encode message).length ≤ 1835092 := by
  have bound_oddLotBidAdfFormAttachment := message.oddLotBidAdfFormAttachment.length_lt
  have bound_oddLotAskAdfFormAttachment := message.oddLotAskAdfFormAttachment.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, Cond.encode_length, Rii.encode_length, BboCond.encode_length, encodeMany_length_const OddLotBidAdfFormAttachment.encode 14 OddLotBidAdfFormAttachment.encode_length, encodeMany_length_const OddLotAskAdfFormAttachment.encode 14 OddLotAskAdfFormAttachment.encode_length]
  omega

@[simp] theorem decode_encode (message : FinraAdfCombinedQuoteMessageWithBbo) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Cond.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Rii.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BboCond.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 2 OddLotBidAdfFormAttachment.encode OddLotBidAdfFormAttachment.decode OddLotBidAdfFormAttachment.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 OddLotAskAdfFormAttachment.encode OddLotAskAdfFormAttachment.decode OddLotAskAdfFormAttachment.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.oddLotBidAdfFormAttachment.length_lt, dite_eq_left message.oddLotAskAdfFormAttachment.length_lt]
  rfl

end FinraAdfCombinedQuoteMessageWithBbo

/-- Any Inbound Quote Messages Message Payload, selected by Inbound Quote Messages Message Type -/
inductive InboundQuoteMessagesMessagePayload where
  | protectedExchangeQuoteMessageShortformMessage (message : ProtectedExchangeQuoteMessageShortformMessage) -- "Q" 0x51
  | protectedExchangeQuoteMessageLongformMessage (message : ProtectedExchangeQuoteMessageLongformMessage) -- "L" 0x4C
  | exchangeOddLotQuoteMessageShortFormMessage (message : ExchangeOddLotQuoteMessageShortFormMessage) -- "O" 0x4F
  | exchangeOddLotQuoteMessageLongFormMessage (message : ExchangeOddLotQuoteMessageLongFormMessage) -- "J" 0x4A
  | exchangeCombinedQuoteMessageShortFormMessage (message : ExchangeCombinedQuoteMessageShortFormMessage) -- "P" 0x50
  | exchangeCombinedQuoteMessageLongFormMessage (message : ExchangeCombinedQuoteMessageLongFormMessage) -- "K" 0x4B
  | finraProtectedQuoteMessageWithBboInfoMessage (message : FinraProtectedQuoteMessageWithBboInfoMessage) -- "G" 0x47
  | finraProtectedQuoteMessageWithoutBboInfoMessage (message : FinraProtectedQuoteMessageWithoutBboInfoMessage) -- "F" 0x46
  | finraAdfOddLotQuotationMessage (message : FinraAdfOddLotQuotationMessage) -- "H" 0x48
  | finraAdfCombinedQuoteMessageWithBbo (message : FinraAdfCombinedQuoteMessageWithBbo) -- "R" 0x52
  deriving DecidableEq, Repr

namespace InboundQuoteMessagesMessagePayload

/-- The Inbound Quote Messages Message Type each message is sent under -/
def tag : InboundQuoteMessagesMessagePayload → BitVec 8
  | .protectedExchangeQuoteMessageShortformMessage _ => 81
  | .protectedExchangeQuoteMessageLongformMessage _ => 76
  | .exchangeOddLotQuoteMessageShortFormMessage _ => 79
  | .exchangeOddLotQuoteMessageLongFormMessage _ => 74
  | .exchangeCombinedQuoteMessageShortFormMessage _ => 80
  | .exchangeCombinedQuoteMessageLongFormMessage _ => 75
  | .finraProtectedQuoteMessageWithBboInfoMessage _ => 71
  | .finraProtectedQuoteMessageWithoutBboInfoMessage _ => 70
  | .finraAdfOddLotQuotationMessage _ => 72
  | .finraAdfCombinedQuoteMessageWithBbo _ => 82

def encode : InboundQuoteMessagesMessagePayload → List UInt8
  | .protectedExchangeQuoteMessageShortformMessage message => ProtectedExchangeQuoteMessageShortformMessage.encode message
  | .protectedExchangeQuoteMessageLongformMessage message => ProtectedExchangeQuoteMessageLongformMessage.encode message
  | .exchangeOddLotQuoteMessageShortFormMessage message => ExchangeOddLotQuoteMessageShortFormMessage.encode message
  | .exchangeOddLotQuoteMessageLongFormMessage message => ExchangeOddLotQuoteMessageLongFormMessage.encode message
  | .exchangeCombinedQuoteMessageShortFormMessage message => ExchangeCombinedQuoteMessageShortFormMessage.encode message
  | .exchangeCombinedQuoteMessageLongFormMessage message => ExchangeCombinedQuoteMessageLongFormMessage.encode message
  | .finraProtectedQuoteMessageWithBboInfoMessage message => FinraProtectedQuoteMessageWithBboInfoMessage.encode message
  | .finraProtectedQuoteMessageWithoutBboInfoMessage message => FinraProtectedQuoteMessageWithoutBboInfoMessage.encode message
  | .finraAdfOddLotQuotationMessage message => FinraAdfOddLotQuotationMessage.encode message
  | .finraAdfCombinedQuoteMessageWithBbo message => FinraAdfCombinedQuoteMessageWithBbo.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : InboundQuoteMessagesMessagePayload) : (encode message).length ≤ 1835092 := by
  cases message with
  | protectedExchangeQuoteMessageShortformMessage inner =>
    simp only [encode, ProtectedExchangeQuoteMessageShortformMessage.encode_length]
    omega
  | protectedExchangeQuoteMessageLongformMessage inner =>
    simp only [encode, ProtectedExchangeQuoteMessageLongformMessage.encode_length]
    omega
  | exchangeOddLotQuoteMessageShortFormMessage inner =>
    have bound_inner := ExchangeOddLotQuoteMessageShortFormMessage.encode_length_le inner
    simp only [encode]
    omega
  | exchangeOddLotQuoteMessageLongFormMessage inner =>
    have bound_inner := ExchangeOddLotQuoteMessageLongFormMessage.encode_length_le inner
    simp only [encode]
    omega
  | exchangeCombinedQuoteMessageShortFormMessage inner =>
    have bound_inner := ExchangeCombinedQuoteMessageShortFormMessage.encode_length_le inner
    simp only [encode]
    omega
  | exchangeCombinedQuoteMessageLongFormMessage inner =>
    have bound_inner := ExchangeCombinedQuoteMessageLongFormMessage.encode_length_le inner
    simp only [encode]
    omega
  | finraProtectedQuoteMessageWithBboInfoMessage inner =>
    simp only [encode, FinraProtectedQuoteMessageWithBboInfoMessage.encode_length]
    omega
  | finraProtectedQuoteMessageWithoutBboInfoMessage inner =>
    simp only [encode, FinraProtectedQuoteMessageWithoutBboInfoMessage.encode_length]
    omega
  | finraAdfOddLotQuotationMessage inner =>
    have bound_inner := FinraAdfOddLotQuotationMessage.encode_length_le inner
    simp only [encode]
    omega
  | finraAdfCombinedQuoteMessageWithBbo inner =>
    have bound_inner := FinraAdfCombinedQuoteMessageWithBbo.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (InboundQuoteMessagesMessagePayload × List UInt8) :=
  if tag = 81 then (ProtectedExchangeQuoteMessageShortformMessage.decode bytes).map fun (message, rest) => (.protectedExchangeQuoteMessageShortformMessage message, rest)
  else if tag = 76 then (ProtectedExchangeQuoteMessageLongformMessage.decode bytes).map fun (message, rest) => (.protectedExchangeQuoteMessageLongformMessage message, rest)
  else if tag = 79 then (ExchangeOddLotQuoteMessageShortFormMessage.decode bytes).map fun (message, rest) => (.exchangeOddLotQuoteMessageShortFormMessage message, rest)
  else if tag = 74 then (ExchangeOddLotQuoteMessageLongFormMessage.decode bytes).map fun (message, rest) => (.exchangeOddLotQuoteMessageLongFormMessage message, rest)
  else if tag = 80 then (ExchangeCombinedQuoteMessageShortFormMessage.decode bytes).map fun (message, rest) => (.exchangeCombinedQuoteMessageShortFormMessage message, rest)
  else if tag = 75 then (ExchangeCombinedQuoteMessageLongFormMessage.decode bytes).map fun (message, rest) => (.exchangeCombinedQuoteMessageLongFormMessage message, rest)
  else if tag = 71 then (FinraProtectedQuoteMessageWithBboInfoMessage.decode bytes).map fun (message, rest) => (.finraProtectedQuoteMessageWithBboInfoMessage message, rest)
  else if tag = 70 then (FinraProtectedQuoteMessageWithoutBboInfoMessage.decode bytes).map fun (message, rest) => (.finraProtectedQuoteMessageWithoutBboInfoMessage message, rest)
  else if tag = 72 then (FinraAdfOddLotQuotationMessage.decode bytes).map fun (message, rest) => (.finraAdfOddLotQuotationMessage message, rest)
  else if tag = 82 then (FinraAdfCombinedQuoteMessageWithBbo.decode bytes).map fun (message, rest) => (.finraAdfCombinedQuoteMessageWithBbo message, rest)
  else none

@[simp] theorem decode_encode (message : InboundQuoteMessagesMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end InboundQuoteMessagesMessagePayload

/-- Inbound Quote Messages Message -/
structure InboundQuoteMessagesMessage where
  inboundQuoteMessagesMessagePayload : InboundQuoteMessagesMessagePayload
  deriving DecidableEq, Repr

namespace InboundQuoteMessagesMessage

def encode (message : InboundQuoteMessagesMessage) : List UInt8 :=
  encodeUInt 1 (InboundQuoteMessagesMessagePayload.tag message.inboundQuoteMessagesMessagePayload)
    ++ (InboundQuoteMessagesMessagePayload.encode message.inboundQuoteMessagesMessagePayload)

def decode (bytes : List UInt8) : Option (InboundQuoteMessagesMessage × List UInt8) := do
  let (inboundQuoteMessagesMessageType, bytes) ← decodeUInt 1 bytes
  let (inboundQuoteMessagesMessagePayload, bytes) ← InboundQuoteMessagesMessagePayload.decode inboundQuoteMessagesMessageType bytes
  pure ({ inboundQuoteMessagesMessagePayload }, bytes)

theorem encode_length_pos (message : InboundQuoteMessagesMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InboundQuoteMessagesMessage) : (encode message).length ≤ 1835093 := by
  unfold encode
  cases message.inboundQuoteMessagesMessagePayload with
  | protectedExchangeQuoteMessageShortformMessage inner =>
    simp only [InboundQuoteMessagesMessagePayload.encode, List.length_append, encodeUInt_length, ProtectedExchangeQuoteMessageShortformMessage.encode_length]
    omega
  | protectedExchangeQuoteMessageLongformMessage inner =>
    simp only [InboundQuoteMessagesMessagePayload.encode, List.length_append, encodeUInt_length, ProtectedExchangeQuoteMessageLongformMessage.encode_length]
    omega
  | exchangeOddLotQuoteMessageShortFormMessage inner =>
    have bound_inner := ExchangeOddLotQuoteMessageShortFormMessage.encode_length_le inner
    simp only [InboundQuoteMessagesMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | exchangeOddLotQuoteMessageLongFormMessage inner =>
    have bound_inner := ExchangeOddLotQuoteMessageLongFormMessage.encode_length_le inner
    simp only [InboundQuoteMessagesMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | exchangeCombinedQuoteMessageShortFormMessage inner =>
    have bound_inner := ExchangeCombinedQuoteMessageShortFormMessage.encode_length_le inner
    simp only [InboundQuoteMessagesMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | exchangeCombinedQuoteMessageLongFormMessage inner =>
    have bound_inner := ExchangeCombinedQuoteMessageLongFormMessage.encode_length_le inner
    simp only [InboundQuoteMessagesMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | finraProtectedQuoteMessageWithBboInfoMessage inner =>
    simp only [InboundQuoteMessagesMessagePayload.encode, List.length_append, encodeUInt_length, FinraProtectedQuoteMessageWithBboInfoMessage.encode_length]
    omega
  | finraProtectedQuoteMessageWithoutBboInfoMessage inner =>
    simp only [InboundQuoteMessagesMessagePayload.encode, List.length_append, encodeUInt_length, FinraProtectedQuoteMessageWithoutBboInfoMessage.encode_length]
    omega
  | finraAdfOddLotQuotationMessage inner =>
    have bound_inner := FinraAdfOddLotQuotationMessage.encode_length_le inner
    simp only [InboundQuoteMessagesMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | finraAdfCombinedQuoteMessageWithBbo inner =>
    have bound_inner := FinraAdfCombinedQuoteMessageWithBbo.encode_length_le inner
    simp only [InboundQuoteMessagesMessagePayload.encode, List.length_append, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : InboundQuoteMessagesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [InboundQuoteMessagesMessagePayload.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InboundQuoteMessagesMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end InboundQuoteMessagesMessage

/-- Regular Trade Report Message: 69 bytes -/
structure RegularTradeReportMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  timestamp2 : BitVec 64
  symbolLong : Alpha 11
  tradeId : BitVec 32
  ttExempt : TtExempt
  trcond : Alpha 4
  ssday : BitVec 16
  side : Side
  price : BitVec 64
  volume : BitVec 32
  deriving DecidableEq, Repr

namespace RegularTradeReportMessage

def encode (message : RegularTradeReportMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (encodeUInt 8 message.timestamp2
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 4 message.tradeId
    ++ (TtExempt.encode message.ttExempt
    ++ (Alpha.encode message.trcond
    ++ (encodeUInt 2 message.ssday
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.volume))))))))))))

def decode (bytes : List UInt8) : Option (RegularTradeReportMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (timestamp2, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradeId, bytes) ← decodeUInt 4 bytes
  let (ttExempt, bytes) ← TtExempt.decode bytes
  let (trcond, bytes) ← Alpha.decode 4 bytes
  let (ssday, bytes) ← decodeUInt 2 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  pure ({ orig, timestamp1, feedSequence, partToken, timestamp2, symbolLong, tradeId, ttExempt, trcond, ssday, side, price, volume }, bytes)

@[simp] theorem encode_length (message : RegularTradeReportMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, TtExempt.encode_length, Side.encode_length]

theorem encode_length_pos (message : RegularTradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegularTradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TtExempt.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RegularTradeReportMessage

/-- Trade Cancel Error Message: 70 bytes -/
structure TradeCancelErrorMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  timestamp2 : BitVec 64
  symbolLong : Alpha 11
  cancelType : CancelType
  origTradeId : BitVec 32
  origTtExempt : Alpha 1
  origTrcond : Alpha 4
  origSsday : BitVec 16
  origSide : Alpha 1
  origPrice : BitVec 64
  origVolume : BitVec 32
  deriving DecidableEq, Repr

namespace TradeCancelErrorMessage

def encode (message : TradeCancelErrorMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (encodeUInt 8 message.timestamp2
    ++ (Alpha.encode message.symbolLong
    ++ (CancelType.encode message.cancelType
    ++ (encodeUInt 4 message.origTradeId
    ++ (Alpha.encode message.origTtExempt
    ++ (Alpha.encode message.origTrcond
    ++ (encodeUInt 2 message.origSsday
    ++ (Alpha.encode message.origSide
    ++ (encodeUInt 8 message.origPrice
    ++ (encodeUInt 4 message.origVolume)))))))))))))

def decode (bytes : List UInt8) : Option (TradeCancelErrorMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (timestamp2, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (cancelType, bytes) ← CancelType.decode bytes
  let (origTradeId, bytes) ← decodeUInt 4 bytes
  let (origTtExempt, bytes) ← Alpha.decode 1 bytes
  let (origTrcond, bytes) ← Alpha.decode 4 bytes
  let (origSsday, bytes) ← decodeUInt 2 bytes
  let (origSide, bytes) ← Alpha.decode 1 bytes
  let (origPrice, bytes) ← decodeUInt 8 bytes
  let (origVolume, bytes) ← decodeUInt 4 bytes
  pure ({ orig, timestamp1, feedSequence, partToken, timestamp2, symbolLong, cancelType, origTradeId, origTtExempt, origTrcond, origSsday, origSide, origPrice, origVolume }, bytes)

@[simp] theorem encode_length (message : TradeCancelErrorMessage) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, CancelType.encode_length]

theorem encode_length_pos (message : TradeCancelErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CancelType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCancelErrorMessage

/-- Trade Correction Message: 92 bytes -/
structure TradeCorrectionMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  timestamp2 : BitVec 64
  symbolLong : Alpha 11
  tradeId : BitVec 32
  origTradeId : BitVec 32
  origTtExempt : Alpha 1
  origTrcond : Alpha 4
  origSsday : BitVec 16
  side : Side
  origPrice : BitVec 64
  origVolume : BitVec 32
  newTtExempt : Alpha 1
  newTrcond : Alpha 4
  newSsday : BitVec 16
  newPrice : BitVec 64
  newVolume : BitVec 32
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (encodeUInt 8 message.timestamp2
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 4 message.tradeId
    ++ (encodeUInt 4 message.origTradeId
    ++ (Alpha.encode message.origTtExempt
    ++ (Alpha.encode message.origTrcond
    ++ (encodeUInt 2 message.origSsday
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.origPrice
    ++ (encodeUInt 4 message.origVolume
    ++ (Alpha.encode message.newTtExempt
    ++ (Alpha.encode message.newTrcond
    ++ (encodeUInt 2 message.newSsday
    ++ (encodeUInt 8 message.newPrice
    ++ (encodeUInt 4 message.newVolume))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (timestamp2, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradeId, bytes) ← decodeUInt 4 bytes
  let (origTradeId, bytes) ← decodeUInt 4 bytes
  let (origTtExempt, bytes) ← Alpha.decode 1 bytes
  let (origTrcond, bytes) ← Alpha.decode 4 bytes
  let (origSsday, bytes) ← decodeUInt 2 bytes
  let (side, bytes) ← Side.decode bytes
  let (origPrice, bytes) ← decodeUInt 8 bytes
  let (origVolume, bytes) ← decodeUInt 4 bytes
  let (newTtExempt, bytes) ← Alpha.decode 1 bytes
  let (newTrcond, bytes) ← Alpha.decode 4 bytes
  let (newSsday, bytes) ← decodeUInt 2 bytes
  let (newPrice, bytes) ← decodeUInt 8 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  pure ({ orig, timestamp1, feedSequence, partToken, timestamp2, symbolLong, tradeId, origTradeId, origTtExempt, origTrcond, origSsday, side, origPrice, origVolume, newTtExempt, newTrcond, newSsday, newPrice, newVolume }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 92 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCorrectionMessage

/-- As Of Trade Report Message: 70 bytes -/
structure AsOfTradeReportMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolLong : Alpha 11
  tradeId : BitVec 32
  ttExempt : TtExempt
  trcond : Alpha 4
  ssday : BitVec 16
  side : Side
  price : BitVec 64
  volume : BitVec 32
  tradeTime : BitVec 64
  reversal : Reversal
  deriving DecidableEq, Repr

namespace AsOfTradeReportMessage

def encode (message : AsOfTradeReportMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 4 message.tradeId
    ++ (TtExempt.encode message.ttExempt
    ++ (Alpha.encode message.trcond
    ++ (encodeUInt 2 message.ssday
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 8 message.tradeTime
    ++ (Reversal.encode message.reversal)))))))))))))

def decode (bytes : List UInt8) : Option (AsOfTradeReportMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradeId, bytes) ← decodeUInt 4 bytes
  let (ttExempt, bytes) ← TtExempt.decode bytes
  let (trcond, bytes) ← Alpha.decode 4 bytes
  let (ssday, bytes) ← decodeUInt 2 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (tradeTime, bytes) ← decodeUInt 8 bytes
  let (reversal, bytes) ← Reversal.decode bytes
  pure ({ orig, timestamp1, feedSequence, partToken, symbolLong, tradeId, ttExempt, trcond, ssday, side, price, volume, tradeTime, reversal }, bytes)

@[simp] theorem encode_length (message : AsOfTradeReportMessage) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, TtExempt.encode_length, Side.encode_length, Reversal.encode_length]

theorem encode_length_pos (message : AsOfTradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AsOfTradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, TtExempt.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Reversal.decode_encode, some_bind]
  rfl

end AsOfTradeReportMessage

/-- Fractional Regular Trade Report Message: 73 bytes -/
structure FractionalRegularTradeReportMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  timestamp2 : BitVec 64
  symbolLong : Alpha 11
  tradeId : BitVec 32
  ttExempt : TtExempt
  trcond : Alpha 4
  ssday : BitVec 16
  side : Side
  price : BitVec 64
  volumeFractional : BitVec 64
  deriving DecidableEq, Repr

namespace FractionalRegularTradeReportMessage

def encode (message : FractionalRegularTradeReportMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (encodeUInt 8 message.timestamp2
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 4 message.tradeId
    ++ (TtExempt.encode message.ttExempt
    ++ (Alpha.encode message.trcond
    ++ (encodeUInt 2 message.ssday
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.volumeFractional))))))))))))

def decode (bytes : List UInt8) : Option (FractionalRegularTradeReportMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (timestamp2, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradeId, bytes) ← decodeUInt 4 bytes
  let (ttExempt, bytes) ← TtExempt.decode bytes
  let (trcond, bytes) ← Alpha.decode 4 bytes
  let (ssday, bytes) ← decodeUInt 2 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (volumeFractional, bytes) ← decodeUInt 8 bytes
  pure ({ orig, timestamp1, feedSequence, partToken, timestamp2, symbolLong, tradeId, ttExempt, trcond, ssday, side, price, volumeFractional }, bytes)

@[simp] theorem encode_length (message : FractionalRegularTradeReportMessage) : (encode message).length = 73 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, TtExempt.encode_length, Side.encode_length]

theorem encode_length_pos (message : FractionalRegularTradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FractionalRegularTradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TtExempt.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FractionalRegularTradeReportMessage

/-- Fractional Trade Cancel Error Message: 74 bytes -/
structure FractionalTradeCancelErrorMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  timestamp2 : BitVec 64
  symbolLong : Alpha 11
  cancelType : CancelType
  origTradeId : BitVec 32
  origTtExempt : Alpha 1
  origTrcond : Alpha 4
  origSsday : BitVec 16
  origSide : Alpha 1
  origPrice : BitVec 64
  origVolumeFractional : BitVec 64
  deriving DecidableEq, Repr

namespace FractionalTradeCancelErrorMessage

def encode (message : FractionalTradeCancelErrorMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (encodeUInt 8 message.timestamp2
    ++ (Alpha.encode message.symbolLong
    ++ (CancelType.encode message.cancelType
    ++ (encodeUInt 4 message.origTradeId
    ++ (Alpha.encode message.origTtExempt
    ++ (Alpha.encode message.origTrcond
    ++ (encodeUInt 2 message.origSsday
    ++ (Alpha.encode message.origSide
    ++ (encodeUInt 8 message.origPrice
    ++ (encodeUInt 8 message.origVolumeFractional)))))))))))))

def decode (bytes : List UInt8) : Option (FractionalTradeCancelErrorMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (timestamp2, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (cancelType, bytes) ← CancelType.decode bytes
  let (origTradeId, bytes) ← decodeUInt 4 bytes
  let (origTtExempt, bytes) ← Alpha.decode 1 bytes
  let (origTrcond, bytes) ← Alpha.decode 4 bytes
  let (origSsday, bytes) ← decodeUInt 2 bytes
  let (origSide, bytes) ← Alpha.decode 1 bytes
  let (origPrice, bytes) ← decodeUInt 8 bytes
  let (origVolumeFractional, bytes) ← decodeUInt 8 bytes
  pure ({ orig, timestamp1, feedSequence, partToken, timestamp2, symbolLong, cancelType, origTradeId, origTtExempt, origTrcond, origSsday, origSide, origPrice, origVolumeFractional }, bytes)

@[simp] theorem encode_length (message : FractionalTradeCancelErrorMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, CancelType.encode_length]

theorem encode_length_pos (message : FractionalTradeCancelErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FractionalTradeCancelErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CancelType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FractionalTradeCancelErrorMessage

/-- Fractional Trade Correction Message: 100 bytes -/
structure FractionalTradeCorrectionMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  timestamp2 : BitVec 64
  symbolLong : Alpha 11
  tradeId : BitVec 32
  origTradeId : BitVec 32
  origTtExempt : Alpha 1
  origTrcond : Alpha 4
  origSsday : BitVec 16
  side : Side
  origPrice : BitVec 64
  origVolumeFractional : BitVec 64
  newTtExempt : Alpha 1
  newTrcond : Alpha 4
  newSsday : BitVec 16
  newPrice : BitVec 64
  newVolumeFractional : BitVec 64
  deriving DecidableEq, Repr

namespace FractionalTradeCorrectionMessage

def encode (message : FractionalTradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (encodeUInt 8 message.timestamp2
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 4 message.tradeId
    ++ (encodeUInt 4 message.origTradeId
    ++ (Alpha.encode message.origTtExempt
    ++ (Alpha.encode message.origTrcond
    ++ (encodeUInt 2 message.origSsday
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.origPrice
    ++ (encodeUInt 8 message.origVolumeFractional
    ++ (Alpha.encode message.newTtExempt
    ++ (Alpha.encode message.newTrcond
    ++ (encodeUInt 2 message.newSsday
    ++ (encodeUInt 8 message.newPrice
    ++ (encodeUInt 8 message.newVolumeFractional))))))))))))))))))

def decode (bytes : List UInt8) : Option (FractionalTradeCorrectionMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (timestamp2, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradeId, bytes) ← decodeUInt 4 bytes
  let (origTradeId, bytes) ← decodeUInt 4 bytes
  let (origTtExempt, bytes) ← Alpha.decode 1 bytes
  let (origTrcond, bytes) ← Alpha.decode 4 bytes
  let (origSsday, bytes) ← decodeUInt 2 bytes
  let (side, bytes) ← Side.decode bytes
  let (origPrice, bytes) ← decodeUInt 8 bytes
  let (origVolumeFractional, bytes) ← decodeUInt 8 bytes
  let (newTtExempt, bytes) ← Alpha.decode 1 bytes
  let (newTrcond, bytes) ← Alpha.decode 4 bytes
  let (newSsday, bytes) ← decodeUInt 2 bytes
  let (newPrice, bytes) ← decodeUInt 8 bytes
  let (newVolumeFractional, bytes) ← decodeUInt 8 bytes
  pure ({ orig, timestamp1, feedSequence, partToken, timestamp2, symbolLong, tradeId, origTradeId, origTtExempt, origTrcond, origSsday, side, origPrice, origVolumeFractional, newTtExempt, newTrcond, newSsday, newPrice, newVolumeFractional }, bytes)

@[simp] theorem encode_length (message : FractionalTradeCorrectionMessage) : (encode message).length = 100 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : FractionalTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FractionalTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FractionalTradeCorrectionMessage

/-- Fractional As Of Trade Report Message: 74 bytes -/
structure FractionalAsOfTradeReportMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolLong : Alpha 11
  tradeId : BitVec 32
  ttExempt : TtExempt
  trcond : Alpha 4
  ssday : BitVec 16
  side : Side
  price : BitVec 64
  volumeFractional : BitVec 64
  tradeTime : BitVec 64
  reversal : Reversal
  deriving DecidableEq, Repr

namespace FractionalAsOfTradeReportMessage

def encode (message : FractionalAsOfTradeReportMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 4 message.tradeId
    ++ (TtExempt.encode message.ttExempt
    ++ (Alpha.encode message.trcond
    ++ (encodeUInt 2 message.ssday
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.volumeFractional
    ++ (encodeUInt 8 message.tradeTime
    ++ (Reversal.encode message.reversal)))))))))))))

def decode (bytes : List UInt8) : Option (FractionalAsOfTradeReportMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradeId, bytes) ← decodeUInt 4 bytes
  let (ttExempt, bytes) ← TtExempt.decode bytes
  let (trcond, bytes) ← Alpha.decode 4 bytes
  let (ssday, bytes) ← decodeUInt 2 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (volumeFractional, bytes) ← decodeUInt 8 bytes
  let (tradeTime, bytes) ← decodeUInt 8 bytes
  let (reversal, bytes) ← Reversal.decode bytes
  pure ({ orig, timestamp1, feedSequence, partToken, symbolLong, tradeId, ttExempt, trcond, ssday, side, price, volumeFractional, tradeTime, reversal }, bytes)

@[simp] theorem encode_length (message : FractionalAsOfTradeReportMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, TtExempt.encode_length, Side.encode_length, Reversal.encode_length]

theorem encode_length_pos (message : FractionalAsOfTradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FractionalAsOfTradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, TtExempt.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Reversal.decode_encode, some_bind]
  rfl

end FractionalAsOfTradeReportMessage

/-- Any Inbound Trade Messages Message Payload, selected by Inbound Trade Messages Message Type -/
inductive InboundTradeMessagesMessagePayload where
  | regularTradeReportMessage (message : RegularTradeReportMessage) -- "E" 0x45
  | tradeCancelErrorMessage (message : TradeCancelErrorMessage) -- "I" 0x49
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "J" 0x4A
  | asOfTradeReportMessage (message : AsOfTradeReportMessage) -- "H" 0x48
  | fractionalRegularTradeReportMessage (message : FractionalRegularTradeReportMessage) -- "K" 0x4B
  | fractionalTradeCancelErrorMessage (message : FractionalTradeCancelErrorMessage) -- "O" 0x4F
  | fractionalTradeCorrectionMessage (message : FractionalTradeCorrectionMessage) -- "P" 0x50
  | fractionalAsOfTradeReportMessage (message : FractionalAsOfTradeReportMessage) -- "Q" 0x51
  deriving DecidableEq, Repr

namespace InboundTradeMessagesMessagePayload

/-- The Inbound Trade Messages Message Type each message is sent under -/
def tag : InboundTradeMessagesMessagePayload → BitVec 8
  | .regularTradeReportMessage _ => 69
  | .tradeCancelErrorMessage _ => 73
  | .tradeCorrectionMessage _ => 74
  | .asOfTradeReportMessage _ => 72
  | .fractionalRegularTradeReportMessage _ => 75
  | .fractionalTradeCancelErrorMessage _ => 79
  | .fractionalTradeCorrectionMessage _ => 80
  | .fractionalAsOfTradeReportMessage _ => 81

def encode : InboundTradeMessagesMessagePayload → List UInt8
  | .regularTradeReportMessage message => RegularTradeReportMessage.encode message
  | .tradeCancelErrorMessage message => TradeCancelErrorMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message
  | .asOfTradeReportMessage message => AsOfTradeReportMessage.encode message
  | .fractionalRegularTradeReportMessage message => FractionalRegularTradeReportMessage.encode message
  | .fractionalTradeCancelErrorMessage message => FractionalTradeCancelErrorMessage.encode message
  | .fractionalTradeCorrectionMessage message => FractionalTradeCorrectionMessage.encode message
  | .fractionalAsOfTradeReportMessage message => FractionalAsOfTradeReportMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : InboundTradeMessagesMessagePayload) : (encode message).length ≤ 100 := by
  cases message with
  | regularTradeReportMessage inner =>
    simp only [encode, RegularTradeReportMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [encode, TradeCancelErrorMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega
  | asOfTradeReportMessage inner =>
    simp only [encode, AsOfTradeReportMessage.encode_length]
    omega
  | fractionalRegularTradeReportMessage inner =>
    simp only [encode, FractionalRegularTradeReportMessage.encode_length]
    omega
  | fractionalTradeCancelErrorMessage inner =>
    simp only [encode, FractionalTradeCancelErrorMessage.encode_length]
    omega
  | fractionalTradeCorrectionMessage inner =>
    simp only [encode, FractionalTradeCorrectionMessage.encode_length]
    omega
  | fractionalAsOfTradeReportMessage inner =>
    simp only [encode, FractionalAsOfTradeReportMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (InboundTradeMessagesMessagePayload × List UInt8) :=
  if tag = 69 then (RegularTradeReportMessage.decode bytes).map fun (message, rest) => (.regularTradeReportMessage message, rest)
  else if tag = 73 then (TradeCancelErrorMessage.decode bytes).map fun (message, rest) => (.tradeCancelErrorMessage message, rest)
  else if tag = 74 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else if tag = 72 then (AsOfTradeReportMessage.decode bytes).map fun (message, rest) => (.asOfTradeReportMessage message, rest)
  else if tag = 75 then (FractionalRegularTradeReportMessage.decode bytes).map fun (message, rest) => (.fractionalRegularTradeReportMessage message, rest)
  else if tag = 79 then (FractionalTradeCancelErrorMessage.decode bytes).map fun (message, rest) => (.fractionalTradeCancelErrorMessage message, rest)
  else if tag = 80 then (FractionalTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.fractionalTradeCorrectionMessage message, rest)
  else if tag = 81 then (FractionalAsOfTradeReportMessage.decode bytes).map fun (message, rest) => (.fractionalAsOfTradeReportMessage message, rest)
  else none

@[simp] theorem decode_encode (message : InboundTradeMessagesMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end InboundTradeMessagesMessagePayload

/-- Inbound Trade Messages Message -/
structure InboundTradeMessagesMessage where
  inboundTradeMessagesMessagePayload : InboundTradeMessagesMessagePayload
  deriving DecidableEq, Repr

namespace InboundTradeMessagesMessage

def encode (message : InboundTradeMessagesMessage) : List UInt8 :=
  encodeUInt 1 (InboundTradeMessagesMessagePayload.tag message.inboundTradeMessagesMessagePayload)
    ++ (InboundTradeMessagesMessagePayload.encode message.inboundTradeMessagesMessagePayload)

def decode (bytes : List UInt8) : Option (InboundTradeMessagesMessage × List UInt8) := do
  let (inboundTradeMessagesMessageType, bytes) ← decodeUInt 1 bytes
  let (inboundTradeMessagesMessagePayload, bytes) ← InboundTradeMessagesMessagePayload.decode inboundTradeMessagesMessageType bytes
  pure ({ inboundTradeMessagesMessagePayload }, bytes)

theorem encode_length_pos (message : InboundTradeMessagesMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InboundTradeMessagesMessage) : (encode message).length ≤ 101 := by
  unfold encode
  cases message.inboundTradeMessagesMessagePayload with
  | regularTradeReportMessage inner =>
    simp only [InboundTradeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, RegularTradeReportMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [InboundTradeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, TradeCancelErrorMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [InboundTradeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, TradeCorrectionMessage.encode_length]
    omega
  | asOfTradeReportMessage inner =>
    simp only [InboundTradeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, AsOfTradeReportMessage.encode_length]
    omega
  | fractionalRegularTradeReportMessage inner =>
    simp only [InboundTradeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, FractionalRegularTradeReportMessage.encode_length]
    omega
  | fractionalTradeCancelErrorMessage inner =>
    simp only [InboundTradeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, FractionalTradeCancelErrorMessage.encode_length]
    omega
  | fractionalTradeCorrectionMessage inner =>
    simp only [InboundTradeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, FractionalTradeCorrectionMessage.encode_length]
    omega
  | fractionalAsOfTradeReportMessage inner =>
    simp only [InboundTradeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, FractionalAsOfTradeReportMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : InboundTradeMessagesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [InboundTradeMessagesMessagePayload.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InboundTradeMessagesMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end InboundTradeMessagesMessage

/-- General Administrative Message -/
structure GeneralAdministrativeMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  textLen : BitVec 16
  text : Capped 65535
  deriving DecidableEq, Repr

namespace GeneralAdministrativeMessage

def encode (message : GeneralAdministrativeMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (encodeUInt 2 message.textLen
    ++ (message.text.val)))))

def decode (bytes : List UInt8) : Option GeneralAdministrativeMessage := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (textLen, bytes) ← decodeUInt 2 bytes
  let text_ := bytes
  if fits_text : text_.length ≤ 65535 then
    pure { orig, timestamp1, feedSequence, partToken, textLen, text := ⟨text_, fits_text⟩ }
  else none

theorem encode_length_pos (message : GeneralAdministrativeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GeneralAdministrativeMessage) : (encode message).length ≤ 65563 := by
  have bound_text := message.text.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length]
  omega

theorem decode_encode (message : GeneralAdministrativeMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.text.length_le]
  rfl

end GeneralAdministrativeMessage

/-- Trading Action Message: 56 bytes -/
structure TradingActionMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolLong : Alpha 11
  action : Action
  actionSequence : BitVec 32
  actionTime : BitVec 64
  reason : Alpha 6
  deriving DecidableEq, Repr

namespace TradingActionMessage

def encode (message : TradingActionMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolLong
    ++ (Action.encode message.action
    ++ (encodeUInt 4 message.actionSequence
    ++ (encodeUInt 8 message.actionTime
    ++ (Alpha.encode message.reason))))))))

def decode (bytes : List UInt8) : Option (TradingActionMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (action, bytes) ← Action.decode bytes
  let (actionSequence, bytes) ← decodeUInt 4 bytes
  let (actionTime, bytes) ← decodeUInt 8 bytes
  let (reason, bytes) ← Alpha.decode 6 bytes
  pure ({ orig, timestamp1, feedSequence, partToken, symbolLong, action, actionSequence, actionTime, reason }, bytes)

@[simp] theorem encode_length (message : TradingActionMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Action.encode_length]

theorem encode_length_pos (message : TradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Action.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradingActionMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradingActionMessage

/-- Market Center Trading Action Message: 46 bytes -/
structure MarketCenterTradingActionMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolLong : Alpha 11
  action : Action
  actionTime : BitVec 64
  deriving DecidableEq, Repr

namespace MarketCenterTradingActionMessage

def encode (message : MarketCenterTradingActionMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolLong
    ++ (Action.encode message.action
    ++ (encodeUInt 8 message.actionTime))))))

def decode (bytes : List UInt8) : Option (MarketCenterTradingActionMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (action, bytes) ← Action.decode bytes
  let (actionTime, bytes) ← decodeUInt 8 bytes
  pure ({ orig, timestamp1, feedSequence, partToken, symbolLong, action, actionTime }, bytes)

@[simp] theorem encode_length (message : MarketCenterTradingActionMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Action.encode_length]

theorem encode_length_pos (message : MarketCenterTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketCenterTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Action.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MarketCenterTradingActionMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MarketCenterTradingActionMessage

/-- Market Center Mass Trading Action Message: 57 bytes -/
structure MarketCenterMassTradingActionMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  firstSecurity : Alpha 11
  lastSecurity : Alpha 11
  action : Action
  actionTime : BitVec 64
  deriving DecidableEq, Repr

namespace MarketCenterMassTradingActionMessage

def encode (message : MarketCenterMassTradingActionMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.firstSecurity
    ++ (Alpha.encode message.lastSecurity
    ++ (Action.encode message.action
    ++ (encodeUInt 8 message.actionTime)))))))

def decode (bytes : List UInt8) : Option (MarketCenterMassTradingActionMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (firstSecurity, bytes) ← Alpha.decode 11 bytes
  let (lastSecurity, bytes) ← Alpha.decode 11 bytes
  let (action, bytes) ← Action.decode bytes
  let (actionTime, bytes) ← decodeUInt 8 bytes
  pure ({ orig, timestamp1, feedSequence, partToken, firstSecurity, lastSecurity, action, actionTime }, bytes)

@[simp] theorem encode_length (message : MarketCenterMassTradingActionMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Action.encode_length]

theorem encode_length_pos (message : MarketCenterMassTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketCenterMassTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Action.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MarketCenterMassTradingActionMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MarketCenterMassTradingActionMessage

/-- Reg Sho Short Sale Price Test Restricted Indicator Message: 38 bytes -/
structure RegShoShortSalePriceTestRestrictedIndicatorMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolLong : Alpha 11
  action : Action
  deriving DecidableEq, Repr

namespace RegShoShortSalePriceTestRestrictedIndicatorMessage

def encode (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolLong
    ++ (Action.encode message.action)))))

def decode (bytes : List UInt8) : Option (RegShoShortSalePriceTestRestrictedIndicatorMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (action, bytes) ← Action.decode bytes
  pure ({ orig, timestamp1, feedSequence, partToken, symbolLong, action }, bytes)

@[simp] theorem encode_length (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Action.encode_length]

theorem encode_length_pos (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Action.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RegShoShortSalePriceTestRestrictedIndicatorMessage

/-- Opening Reference Midpoint Price Message: 45 bytes -/
structure OpeningReferenceMidpointPriceMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolLong : Alpha 11
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OpeningReferenceMidpointPriceMessage

def encode (message : OpeningReferenceMidpointPriceMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 8 message.price)))))

def decode (bytes : List UInt8) : Option (OpeningReferenceMidpointPriceMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ orig, timestamp1, feedSequence, partToken, symbolLong, price }, bytes)

@[simp] theorem encode_length (message : OpeningReferenceMidpointPriceMessage) : (encode message).length = 45 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OpeningReferenceMidpointPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpeningReferenceMidpointPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OpeningReferenceMidpointPriceMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OpeningReferenceMidpointPriceMessage

/-- T 1 Adjusted Closing Price Message: 45 bytes -/
structure T1AdjustedClosingPriceMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolLong : Alpha 11
  price : BitVec 64
  deriving DecidableEq, Repr

namespace T1AdjustedClosingPriceMessage

def encode (message : T1AdjustedClosingPriceMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 8 message.price)))))

def decode (bytes : List UInt8) : Option (T1AdjustedClosingPriceMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ orig, timestamp1, feedSequence, partToken, symbolLong, price }, bytes)

@[simp] theorem encode_length (message : T1AdjustedClosingPriceMessage) : (encode message).length = 45 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : T1AdjustedClosingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : T1AdjustedClosingPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : T1AdjustedClosingPriceMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end T1AdjustedClosingPriceMessage

/-- Market Open Message: 26 bytes -/
structure MarketOpenMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  deriving DecidableEq, Repr

namespace MarketOpenMessage

def encode (message : MarketOpenMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken)))

def decode (bytes : List UInt8) : Option (MarketOpenMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  pure ({ orig, timestamp1, feedSequence, partToken }, bytes)

@[simp] theorem encode_length (message : MarketOpenMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MarketOpenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketOpenMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MarketOpenMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MarketOpenMessage

/-- Market Closed Message: 26 bytes -/
structure MarketClosedMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  deriving DecidableEq, Repr

namespace MarketClosedMessage

def encode (message : MarketClosedMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken)))

def decode (bytes : List UInt8) : Option (MarketClosedMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  pure ({ orig, timestamp1, feedSequence, partToken }, bytes)

@[simp] theorem encode_length (message : MarketClosedMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MarketClosedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketClosedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MarketClosedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MarketClosedMessage

/-- Auction Collar Message: 66 bytes -/
structure AuctionCollarMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolLong : Alpha 11
  actionSequence : BitVec 32
  collarReferencePrice : BitVec 64
  collarUpPrice : BitVec 64
  collarDownPrice : BitVec 64
  collarExtension : Alpha 1
  deriving DecidableEq, Repr

namespace AuctionCollarMessage

def encode (message : AuctionCollarMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 4 message.actionSequence
    ++ (encodeUInt 8 message.collarReferencePrice
    ++ (encodeUInt 8 message.collarUpPrice
    ++ (encodeUInt 8 message.collarDownPrice
    ++ (Alpha.encode message.collarExtension)))))))))

def decode (bytes : List UInt8) : Option (AuctionCollarMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (actionSequence, bytes) ← decodeUInt 4 bytes
  let (collarReferencePrice, bytes) ← decodeUInt 8 bytes
  let (collarUpPrice, bytes) ← decodeUInt 8 bytes
  let (collarDownPrice, bytes) ← decodeUInt 8 bytes
  let (collarExtension, bytes) ← Alpha.decode 1 bytes
  pure ({ orig, timestamp1, feedSequence, partToken, symbolLong, actionSequence, collarReferencePrice, collarUpPrice, collarDownPrice, collarExtension }, bytes)

@[simp] theorem encode_length (message : AuctionCollarMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AuctionCollarMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionCollarMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : AuctionCollarMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end AuctionCollarMessage

/-- Any Inbound Administrative Messages Message Payload, selected by Inbound Administrative Messages Message Type -/
inductive InboundAdministrativeMessagesMessagePayload where
  | generalAdministrativeMessage (message : GeneralAdministrativeMessage) -- "A" 0x41
  | tradingActionMessage (message : TradingActionMessage) -- "O" 0x4F
  | marketCenterTradingActionMessage (message : MarketCenterTradingActionMessage) -- "J" 0x4A
  | marketCenterMassTradingActionMessage (message : MarketCenterMassTradingActionMessage) -- "U" 0x55
  | regShoShortSalePriceTestRestrictedIndicatorMessage (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) -- "V" 0x56
  | openingReferenceMidpointPriceMessage (message : OpeningReferenceMidpointPriceMessage) -- "M" 0x4D
  | t1AdjustedClosingPriceMessage (message : T1AdjustedClosingPriceMessage) -- "N" 0x4E
  | marketOpenMessage (message : MarketOpenMessage) -- "X" 0x58
  | marketClosedMessage (message : MarketClosedMessage) -- "Y" 0x59
  | auctionCollarMessage (message : AuctionCollarMessage) -- "E" 0x45
  deriving DecidableEq, Repr

namespace InboundAdministrativeMessagesMessagePayload

/-- The Inbound Administrative Messages Message Type each message is sent under -/
def tag : InboundAdministrativeMessagesMessagePayload → BitVec 8
  | .generalAdministrativeMessage _ => 65
  | .tradingActionMessage _ => 79
  | .marketCenterTradingActionMessage _ => 74
  | .marketCenterMassTradingActionMessage _ => 85
  | .regShoShortSalePriceTestRestrictedIndicatorMessage _ => 86
  | .openingReferenceMidpointPriceMessage _ => 77
  | .t1AdjustedClosingPriceMessage _ => 78
  | .marketOpenMessage _ => 88
  | .marketClosedMessage _ => 89
  | .auctionCollarMessage _ => 69

def encode : InboundAdministrativeMessagesMessagePayload → List UInt8
  | .generalAdministrativeMessage message => GeneralAdministrativeMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .marketCenterTradingActionMessage message => MarketCenterTradingActionMessage.encode message
  | .marketCenterMassTradingActionMessage message => MarketCenterMassTradingActionMessage.encode message
  | .regShoShortSalePriceTestRestrictedIndicatorMessage message => RegShoShortSalePriceTestRestrictedIndicatorMessage.encode message
  | .openingReferenceMidpointPriceMessage message => OpeningReferenceMidpointPriceMessage.encode message
  | .t1AdjustedClosingPriceMessage message => T1AdjustedClosingPriceMessage.encode message
  | .marketOpenMessage message => MarketOpenMessage.encode message
  | .marketClosedMessage message => MarketClosedMessage.encode message
  | .auctionCollarMessage message => AuctionCollarMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : InboundAdministrativeMessagesMessagePayload) : (encode message).length ≤ 65563 := by
  cases message with
  | generalAdministrativeMessage inner =>
    have bound_inner := GeneralAdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega
  | tradingActionMessage inner =>
    simp only [encode, TradingActionMessage.encode_length]
    omega
  | marketCenterTradingActionMessage inner =>
    simp only [encode, MarketCenterTradingActionMessage.encode_length]
    omega
  | marketCenterMassTradingActionMessage inner =>
    simp only [encode, MarketCenterMassTradingActionMessage.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [encode, RegShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | openingReferenceMidpointPriceMessage inner =>
    simp only [encode, OpeningReferenceMidpointPriceMessage.encode_length]
    omega
  | t1AdjustedClosingPriceMessage inner =>
    simp only [encode, T1AdjustedClosingPriceMessage.encode_length]
    omega
  | marketOpenMessage inner =>
    simp only [encode, MarketOpenMessage.encode_length]
    omega
  | marketClosedMessage inner =>
    simp only [encode, MarketClosedMessage.encode_length]
    omega
  | auctionCollarMessage inner =>
    simp only [encode, AuctionCollarMessage.encode_length]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option InboundAdministrativeMessagesMessagePayload :=
  if tag = 65 then (GeneralAdministrativeMessage.decode bytes).map fun message => .generalAdministrativeMessage message
  else if tag = 79 then (TradingActionMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradingActionMessage message) else none
  else if tag = 74 then (MarketCenterTradingActionMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.marketCenterTradingActionMessage message) else none
  else if tag = 85 then (MarketCenterMassTradingActionMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.marketCenterMassTradingActionMessage message) else none
  else if tag = 86 then (RegShoShortSalePriceTestRestrictedIndicatorMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.regShoShortSalePriceTestRestrictedIndicatorMessage message) else none
  else if tag = 77 then (OpeningReferenceMidpointPriceMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.openingReferenceMidpointPriceMessage message) else none
  else if tag = 78 then (T1AdjustedClosingPriceMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.t1AdjustedClosingPriceMessage message) else none
  else if tag = 88 then (MarketOpenMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.marketOpenMessage message) else none
  else if tag = 89 then (MarketClosedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.marketClosedMessage message) else none
  else if tag = 69 then (AuctionCollarMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.auctionCollarMessage message) else none
  else none

theorem decode_encode (message : InboundAdministrativeMessagesMessagePayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | generalAdministrativeMessage message => simp [decode, encode, tag, GeneralAdministrativeMessage.decode_encode]
  | tradingActionMessage message => simp [decode, encode, tag, TradingActionMessage.decode_encode_nil]
  | marketCenterTradingActionMessage message => simp [decode, encode, tag, MarketCenterTradingActionMessage.decode_encode_nil]
  | marketCenterMassTradingActionMessage message => simp [decode, encode, tag, MarketCenterMassTradingActionMessage.decode_encode_nil]
  | regShoShortSalePriceTestRestrictedIndicatorMessage message => simp [decode, encode, tag, RegShoShortSalePriceTestRestrictedIndicatorMessage.decode_encode_nil]
  | openingReferenceMidpointPriceMessage message => simp [decode, encode, tag, OpeningReferenceMidpointPriceMessage.decode_encode_nil]
  | t1AdjustedClosingPriceMessage message => simp [decode, encode, tag, T1AdjustedClosingPriceMessage.decode_encode_nil]
  | marketOpenMessage message => simp [decode, encode, tag, MarketOpenMessage.decode_encode_nil]
  | marketClosedMessage message => simp [decode, encode, tag, MarketClosedMessage.decode_encode_nil]
  | auctionCollarMessage message => simp [decode, encode, tag, AuctionCollarMessage.decode_encode_nil]

end InboundAdministrativeMessagesMessagePayload

/-- Inbound Administrative Messages Message -/
structure InboundAdministrativeMessagesMessage where
  inboundAdministrativeMessagesMessagePayload : InboundAdministrativeMessagesMessagePayload
  deriving DecidableEq, Repr

namespace InboundAdministrativeMessagesMessage

def encode (message : InboundAdministrativeMessagesMessage) : List UInt8 :=
  encodeUInt 1 (InboundAdministrativeMessagesMessagePayload.tag message.inboundAdministrativeMessagesMessagePayload)
    ++ (InboundAdministrativeMessagesMessagePayload.encode message.inboundAdministrativeMessagesMessagePayload)

def decode (bytes : List UInt8) : Option InboundAdministrativeMessagesMessage := do
  let (inboundAdministrativeMessagesMessageType, bytes) ← decodeUInt 1 bytes
  let inboundAdministrativeMessagesMessagePayload ← InboundAdministrativeMessagesMessagePayload.decode inboundAdministrativeMessagesMessageType bytes
  pure { inboundAdministrativeMessagesMessagePayload }

theorem encode_length_pos (message : InboundAdministrativeMessagesMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InboundAdministrativeMessagesMessage) : (encode message).length ≤ 65564 := by
  unfold encode
  cases message.inboundAdministrativeMessagesMessagePayload with
  | generalAdministrativeMessage inner =>
    have bound_inner := GeneralAdministrativeMessage.encode_length_le inner
    simp only [InboundAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | tradingActionMessage inner =>
    simp only [InboundAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, TradingActionMessage.encode_length]
    omega
  | marketCenterTradingActionMessage inner =>
    simp only [InboundAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, MarketCenterTradingActionMessage.encode_length]
    omega
  | marketCenterMassTradingActionMessage inner =>
    simp only [InboundAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, MarketCenterMassTradingActionMessage.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [InboundAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, RegShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | openingReferenceMidpointPriceMessage inner =>
    simp only [InboundAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, OpeningReferenceMidpointPriceMessage.encode_length]
    omega
  | t1AdjustedClosingPriceMessage inner =>
    simp only [InboundAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, T1AdjustedClosingPriceMessage.encode_length]
    omega
  | marketOpenMessage inner =>
    simp only [InboundAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, MarketOpenMessage.encode_length]
    omega
  | marketClosedMessage inner =>
    simp only [InboundAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, MarketClosedMessage.encode_length]
    omega
  | auctionCollarMessage inner =>
    simp only [InboundAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, AuctionCollarMessage.encode_length]
    omega

theorem decode_encode (message : InboundAdministrativeMessagesMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [InboundAdministrativeMessagesMessagePayload.decode_encode, some_bind]
  rfl

end InboundAdministrativeMessagesMessage

/-- Sequence Inquiry Message: 26 bytes -/
structure SequenceInquiryMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  deriving DecidableEq, Repr

namespace SequenceInquiryMessage

def encode (message : SequenceInquiryMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken)))

def decode (bytes : List UInt8) : Option (SequenceInquiryMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  pure ({ orig, timestamp1, feedSequence, partToken }, bytes)

@[simp] theorem encode_length (message : SequenceInquiryMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SequenceInquiryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceInquiryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SequenceInquiryMessage

/-- Symbol State Inquiry Message: 37 bytes -/
structure SymbolStateInquiryMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  symbolLong : Alpha 11
  deriving DecidableEq, Repr

namespace SymbolStateInquiryMessage

def encode (message : SymbolStateInquiryMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (Alpha.encode message.symbolLong))))

def decode (bytes : List UInt8) : Option (SymbolStateInquiryMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  pure ({ orig, timestamp1, feedSequence, partToken, symbolLong }, bytes)

@[simp] theorem encode_length (message : SymbolStateInquiryMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SymbolStateInquiryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolStateInquiryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolStateInquiryMessage

/-- End Of Participant Reporting Message: 26 bytes -/
structure EndOfParticipantReportingMessage where
  orig : Alpha 2
  timestamp1 : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  deriving DecidableEq, Repr

namespace EndOfParticipantReportingMessage

def encode (message : EndOfParticipantReportingMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.timestamp1
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken)))

def decode (bytes : List UInt8) : Option (EndOfParticipantReportingMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (timestamp1, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  pure ({ orig, timestamp1, feedSequence, partToken }, bytes)

@[simp] theorem encode_length (message : EndOfParticipantReportingMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : EndOfParticipantReportingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfParticipantReportingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndOfParticipantReportingMessage

/-- Any Inbound Control Messages Message Payload, selected by Inbound Control Messages Message Type -/
inductive InboundControlMessagesMessagePayload where
  | sequenceInquiryMessage (message : SequenceInquiryMessage) -- "C" 0x43
  | symbolStateInquiryMessage (message : SymbolStateInquiryMessage) -- "S" 0x53
  | endOfParticipantReportingMessage (message : EndOfParticipantReportingMessage) -- "G" 0x47
  deriving DecidableEq, Repr

namespace InboundControlMessagesMessagePayload

/-- The Inbound Control Messages Message Type each message is sent under -/
def tag : InboundControlMessagesMessagePayload → BitVec 8
  | .sequenceInquiryMessage _ => 67
  | .symbolStateInquiryMessage _ => 83
  | .endOfParticipantReportingMessage _ => 71

def encode : InboundControlMessagesMessagePayload → List UInt8
  | .sequenceInquiryMessage message => SequenceInquiryMessage.encode message
  | .symbolStateInquiryMessage message => SymbolStateInquiryMessage.encode message
  | .endOfParticipantReportingMessage message => EndOfParticipantReportingMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : InboundControlMessagesMessagePayload) : (encode message).length ≤ 37 := by
  cases message with
  | sequenceInquiryMessage inner =>
    simp only [encode, SequenceInquiryMessage.encode_length]
    omega
  | symbolStateInquiryMessage inner =>
    simp only [encode, SymbolStateInquiryMessage.encode_length]
    omega
  | endOfParticipantReportingMessage inner =>
    simp only [encode, EndOfParticipantReportingMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (InboundControlMessagesMessagePayload × List UInt8) :=
  if tag = 67 then (SequenceInquiryMessage.decode bytes).map fun (message, rest) => (.sequenceInquiryMessage message, rest)
  else if tag = 83 then (SymbolStateInquiryMessage.decode bytes).map fun (message, rest) => (.symbolStateInquiryMessage message, rest)
  else if tag = 71 then (EndOfParticipantReportingMessage.decode bytes).map fun (message, rest) => (.endOfParticipantReportingMessage message, rest)
  else none

@[simp] theorem decode_encode (message : InboundControlMessagesMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end InboundControlMessagesMessagePayload

/-- Inbound Control Messages Message -/
structure InboundControlMessagesMessage where
  inboundControlMessagesMessagePayload : InboundControlMessagesMessagePayload
  deriving DecidableEq, Repr

namespace InboundControlMessagesMessage

def encode (message : InboundControlMessagesMessage) : List UInt8 :=
  encodeUInt 1 (InboundControlMessagesMessagePayload.tag message.inboundControlMessagesMessagePayload)
    ++ (InboundControlMessagesMessagePayload.encode message.inboundControlMessagesMessagePayload)

def decode (bytes : List UInt8) : Option (InboundControlMessagesMessage × List UInt8) := do
  let (inboundControlMessagesMessageType, bytes) ← decodeUInt 1 bytes
  let (inboundControlMessagesMessagePayload, bytes) ← InboundControlMessagesMessagePayload.decode inboundControlMessagesMessageType bytes
  pure ({ inboundControlMessagesMessagePayload }, bytes)

theorem encode_length_pos (message : InboundControlMessagesMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InboundControlMessagesMessage) : (encode message).length ≤ 38 := by
  unfold encode
  cases message.inboundControlMessagesMessagePayload with
  | sequenceInquiryMessage inner =>
    simp only [InboundControlMessagesMessagePayload.encode, List.length_append, encodeUInt_length, SequenceInquiryMessage.encode_length]
    omega
  | symbolStateInquiryMessage inner =>
    simp only [InboundControlMessagesMessagePayload.encode, List.length_append, encodeUInt_length, SymbolStateInquiryMessage.encode_length]
    omega
  | endOfParticipantReportingMessage inner =>
    simp only [InboundControlMessagesMessagePayload.encode, List.length_append, encodeUInt_length, EndOfParticipantReportingMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : InboundControlMessagesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [InboundControlMessagesMessagePayload.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InboundControlMessagesMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end InboundControlMessagesMessage

/-- Return General Administrative Message -/
structure ReturnGeneralAdministrativeMessage where
  orig : Alpha 2
  sipTime : BitVec 64
  textLen : BitVec 16
  text : Capped 65535
  deriving DecidableEq, Repr

namespace ReturnGeneralAdministrativeMessage

def encode (message : ReturnGeneralAdministrativeMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.sipTime
    ++ (encodeUInt 2 message.textLen
    ++ (message.text.val)))

def decode (bytes : List UInt8) : Option ReturnGeneralAdministrativeMessage := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (sipTime, bytes) ← decodeUInt 8 bytes
  let (textLen, bytes) ← decodeUInt 2 bytes
  let text_ := bytes
  if fits_text : text_.length ≤ 65535 then
    pure { orig, sipTime, textLen, text := ⟨text_, fits_text⟩ }
  else none

theorem encode_length_pos (message : ReturnGeneralAdministrativeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReturnGeneralAdministrativeMessage) : (encode message).length ≤ 65547 := by
  have bound_text := message.text.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length]
  omega

theorem decode_encode (message : ReturnGeneralAdministrativeMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.text.length_le]
  rfl

end ReturnGeneralAdministrativeMessage

/-- Return Market Center Trading Action Acknowledgement Message: 30 bytes -/
structure ReturnMarketCenterTradingActionAcknowledgementMessage where
  orig : Alpha 2
  sipTime : BitVec 64
  symbolLong : Alpha 11
  action : Action
  actionTime : BitVec 64
  deriving DecidableEq, Repr

namespace ReturnMarketCenterTradingActionAcknowledgementMessage

def encode (message : ReturnMarketCenterTradingActionAcknowledgementMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.sipTime
    ++ (Alpha.encode message.symbolLong
    ++ (Action.encode message.action
    ++ (encodeUInt 8 message.actionTime))))

def decode (bytes : List UInt8) : Option (ReturnMarketCenterTradingActionAcknowledgementMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (sipTime, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (action, bytes) ← Action.decode bytes
  let (actionTime, bytes) ← decodeUInt 8 bytes
  pure ({ orig, sipTime, symbolLong, action, actionTime }, bytes)

@[simp] theorem encode_length (message : ReturnMarketCenterTradingActionAcknowledgementMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Action.encode_length]

theorem encode_length_pos (message : ReturnMarketCenterTradingActionAcknowledgementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReturnMarketCenterTradingActionAcknowledgementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Action.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ReturnMarketCenterTradingActionAcknowledgementMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ReturnMarketCenterTradingActionAcknowledgementMessage

/-- Return Market Open Message: 10 bytes -/
structure ReturnMarketOpenMessage where
  orig : Alpha 2
  sipTime : BitVec 64
  deriving DecidableEq, Repr

namespace ReturnMarketOpenMessage

def encode (message : ReturnMarketOpenMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.sipTime)

def decode (bytes : List UInt8) : Option (ReturnMarketOpenMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (sipTime, bytes) ← decodeUInt 8 bytes
  pure ({ orig, sipTime }, bytes)

@[simp] theorem encode_length (message : ReturnMarketOpenMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ReturnMarketOpenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReturnMarketOpenMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ReturnMarketOpenMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ReturnMarketOpenMessage

/-- Return Market Closed Message: 10 bytes -/
structure ReturnMarketClosedMessage where
  orig : Alpha 2
  sipTime : BitVec 64
  deriving DecidableEq, Repr

namespace ReturnMarketClosedMessage

def encode (message : ReturnMarketClosedMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.sipTime)

def decode (bytes : List UInt8) : Option (ReturnMarketClosedMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (sipTime, bytes) ← decodeUInt 8 bytes
  pure ({ orig, sipTime }, bytes)

@[simp] theorem encode_length (message : ReturnMarketClosedMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ReturnMarketClosedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReturnMarketClosedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ReturnMarketClosedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ReturnMarketClosedMessage

/-- Reject Message: 29 bytes -/
structure RejectMessage where
  orig : Alpha 2
  sipTime : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  rejectCode : BitVec 16
  syntaxViolation : SyntaxViolation
  deriving DecidableEq, Repr

namespace RejectMessage

def encode (message : RejectMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.sipTime
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (encodeUInt 2 message.rejectCode
    ++ (SyntaxViolation.encode message.syntaxViolation)))))

def decode (bytes : List UInt8) : Option (RejectMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (sipTime, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (rejectCode, bytes) ← decodeUInt 2 bytes
  let (syntaxViolation, bytes) ← SyntaxViolation.decode bytes
  pure ({ orig, sipTime, feedSequence, partToken, rejectCode, syntaxViolation }, bytes)

@[simp] theorem encode_length (message : RejectMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, SyntaxViolation.encode_length]

theorem encode_length_pos (message : RejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [SyntaxViolation.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RejectMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RejectMessage

/-- Sequence Acknowledgement Message: 26 bytes -/
structure SequenceAcknowledgementMessage where
  orig : Alpha 2
  sipTime : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  deriving DecidableEq, Repr

namespace SequenceAcknowledgementMessage

def encode (message : SequenceAcknowledgementMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.sipTime
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken)))

def decode (bytes : List UInt8) : Option (SequenceAcknowledgementMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (sipTime, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  pure ({ orig, sipTime, feedSequence, partToken }, bytes)

@[simp] theorem encode_length (message : SequenceAcknowledgementMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SequenceAcknowledgementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceAcknowledgementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequenceAcknowledgementMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequenceAcknowledgementMessage

/-- Participant Input Warning Message: 42 bytes -/
structure ParticipantInputWarningMessage where
  orig : Alpha 2
  sipTime : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  warningCode : BitVec 16
  symbolLong : Alpha 11
  olAttachmenType : Alpha 1
  olAttachmentCount : BitVec 16
  deriving DecidableEq, Repr

namespace ParticipantInputWarningMessage

def encode (message : ParticipantInputWarningMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.sipTime
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (encodeUInt 2 message.warningCode
    ++ (Alpha.encode message.symbolLong
    ++ (Alpha.encode message.olAttachmenType
    ++ (encodeUInt 2 message.olAttachmentCount)))))))

def decode (bytes : List UInt8) : Option (ParticipantInputWarningMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (sipTime, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (warningCode, bytes) ← decodeUInt 2 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (olAttachmenType, bytes) ← Alpha.decode 1 bytes
  let (olAttachmentCount, bytes) ← decodeUInt 2 bytes
  pure ({ orig, sipTime, feedSequence, partToken, warningCode, symbolLong, olAttachmenType, olAttachmentCount }, bytes)

@[simp] theorem encode_length (message : ParticipantInputWarningMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ParticipantInputWarningMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ParticipantInputWarningMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ParticipantInputWarningMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ParticipantInputWarningMessage

/-- Any Return Administrative Messages Message Payload, selected by Return Administrative Messages Message Type -/
inductive ReturnAdministrativeMessagesMessagePayload where
  | returnGeneralAdministrativeMessage (message : ReturnGeneralAdministrativeMessage) -- "A" 0x41
  | returnMarketCenterTradingActionAcknowledgementMessage (message : ReturnMarketCenterTradingActionAcknowledgementMessage) -- "J" 0x4A
  | returnMarketOpenMessage (message : ReturnMarketOpenMessage) -- "X" 0x58
  | returnMarketClosedMessage (message : ReturnMarketClosedMessage) -- "Y" 0x59
  | rejectMessage (message : RejectMessage) -- "R" 0x52
  | sequenceAcknowledgementMessage (message : SequenceAcknowledgementMessage) -- "K" 0x4B
  | participantInputWarningMessage (message : ParticipantInputWarningMessage) -- "W" 0x57
  deriving DecidableEq, Repr

namespace ReturnAdministrativeMessagesMessagePayload

/-- The Return Administrative Messages Message Type each message is sent under -/
def tag : ReturnAdministrativeMessagesMessagePayload → BitVec 8
  | .returnGeneralAdministrativeMessage _ => 65
  | .returnMarketCenterTradingActionAcknowledgementMessage _ => 74
  | .returnMarketOpenMessage _ => 88
  | .returnMarketClosedMessage _ => 89
  | .rejectMessage _ => 82
  | .sequenceAcknowledgementMessage _ => 75
  | .participantInputWarningMessage _ => 87

def encode : ReturnAdministrativeMessagesMessagePayload → List UInt8
  | .returnGeneralAdministrativeMessage message => ReturnGeneralAdministrativeMessage.encode message
  | .returnMarketCenterTradingActionAcknowledgementMessage message => ReturnMarketCenterTradingActionAcknowledgementMessage.encode message
  | .returnMarketOpenMessage message => ReturnMarketOpenMessage.encode message
  | .returnMarketClosedMessage message => ReturnMarketClosedMessage.encode message
  | .rejectMessage message => RejectMessage.encode message
  | .sequenceAcknowledgementMessage message => SequenceAcknowledgementMessage.encode message
  | .participantInputWarningMessage message => ParticipantInputWarningMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ReturnAdministrativeMessagesMessagePayload) : (encode message).length ≤ 65547 := by
  cases message with
  | returnGeneralAdministrativeMessage inner =>
    have bound_inner := ReturnGeneralAdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega
  | returnMarketCenterTradingActionAcknowledgementMessage inner =>
    simp only [encode, ReturnMarketCenterTradingActionAcknowledgementMessage.encode_length]
    omega
  | returnMarketOpenMessage inner =>
    simp only [encode, ReturnMarketOpenMessage.encode_length]
    omega
  | returnMarketClosedMessage inner =>
    simp only [encode, ReturnMarketClosedMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [encode, RejectMessage.encode_length]
    omega
  | sequenceAcknowledgementMessage inner =>
    simp only [encode, SequenceAcknowledgementMessage.encode_length]
    omega
  | participantInputWarningMessage inner =>
    simp only [encode, ParticipantInputWarningMessage.encode_length]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ReturnAdministrativeMessagesMessagePayload :=
  if tag = 65 then (ReturnGeneralAdministrativeMessage.decode bytes).map fun message => .returnGeneralAdministrativeMessage message
  else if tag = 74 then (ReturnMarketCenterTradingActionAcknowledgementMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.returnMarketCenterTradingActionAcknowledgementMessage message) else none
  else if tag = 88 then (ReturnMarketOpenMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.returnMarketOpenMessage message) else none
  else if tag = 89 then (ReturnMarketClosedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.returnMarketClosedMessage message) else none
  else if tag = 82 then (RejectMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.rejectMessage message) else none
  else if tag = 75 then (SequenceAcknowledgementMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequenceAcknowledgementMessage message) else none
  else if tag = 87 then (ParticipantInputWarningMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.participantInputWarningMessage message) else none
  else none

theorem decode_encode (message : ReturnAdministrativeMessagesMessagePayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | returnGeneralAdministrativeMessage message => simp [decode, encode, tag, ReturnGeneralAdministrativeMessage.decode_encode]
  | returnMarketCenterTradingActionAcknowledgementMessage message => simp [decode, encode, tag, ReturnMarketCenterTradingActionAcknowledgementMessage.decode_encode_nil]
  | returnMarketOpenMessage message => simp [decode, encode, tag, ReturnMarketOpenMessage.decode_encode_nil]
  | returnMarketClosedMessage message => simp [decode, encode, tag, ReturnMarketClosedMessage.decode_encode_nil]
  | rejectMessage message => simp [decode, encode, tag, RejectMessage.decode_encode_nil]
  | sequenceAcknowledgementMessage message => simp [decode, encode, tag, SequenceAcknowledgementMessage.decode_encode_nil]
  | participantInputWarningMessage message => simp [decode, encode, tag, ParticipantInputWarningMessage.decode_encode_nil]

end ReturnAdministrativeMessagesMessagePayload

/-- Return Administrative Messages Message -/
structure ReturnAdministrativeMessagesMessage where
  returnAdministrativeMessagesMessagePayload : ReturnAdministrativeMessagesMessagePayload
  deriving DecidableEq, Repr

namespace ReturnAdministrativeMessagesMessage

def encode (message : ReturnAdministrativeMessagesMessage) : List UInt8 :=
  encodeUInt 1 (ReturnAdministrativeMessagesMessagePayload.tag message.returnAdministrativeMessagesMessagePayload)
    ++ (ReturnAdministrativeMessagesMessagePayload.encode message.returnAdministrativeMessagesMessagePayload)

def decode (bytes : List UInt8) : Option ReturnAdministrativeMessagesMessage := do
  let (returnAdministrativeMessagesMessageType, bytes) ← decodeUInt 1 bytes
  let returnAdministrativeMessagesMessagePayload ← ReturnAdministrativeMessagesMessagePayload.decode returnAdministrativeMessagesMessageType bytes
  pure { returnAdministrativeMessagesMessagePayload }

theorem encode_length_pos (message : ReturnAdministrativeMessagesMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReturnAdministrativeMessagesMessage) : (encode message).length ≤ 65548 := by
  unfold encode
  cases message.returnAdministrativeMessagesMessagePayload with
  | returnGeneralAdministrativeMessage inner =>
    have bound_inner := ReturnGeneralAdministrativeMessage.encode_length_le inner
    simp only [ReturnAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | returnMarketCenterTradingActionAcknowledgementMessage inner =>
    simp only [ReturnAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, ReturnMarketCenterTradingActionAcknowledgementMessage.encode_length]
    omega
  | returnMarketOpenMessage inner =>
    simp only [ReturnAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, ReturnMarketOpenMessage.encode_length]
    omega
  | returnMarketClosedMessage inner =>
    simp only [ReturnAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, ReturnMarketClosedMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [ReturnAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, RejectMessage.encode_length]
    omega
  | sequenceAcknowledgementMessage inner =>
    simp only [ReturnAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, SequenceAcknowledgementMessage.encode_length]
    omega
  | participantInputWarningMessage inner =>
    simp only [ReturnAdministrativeMessagesMessagePayload.encode, List.length_append, encodeUInt_length, ParticipantInputWarningMessage.encode_length]
    omega

theorem decode_encode (message : ReturnAdministrativeMessagesMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ReturnAdministrativeMessagesMessagePayload.decode_encode, some_bind]
  rfl

end ReturnAdministrativeMessagesMessage

/-- Start Of Day Message: 10 bytes -/
structure StartOfDayMessage where
  orig : Alpha 2
  sipTime : BitVec 64
  deriving DecidableEq, Repr

namespace StartOfDayMessage

def encode (message : StartOfDayMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.sipTime)

def decode (bytes : List UInt8) : Option (StartOfDayMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (sipTime, bytes) ← decodeUInt 8 bytes
  pure ({ orig, sipTime }, bytes)

@[simp] theorem encode_length (message : StartOfDayMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StartOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfDayMessage

/-- End Of Day Message: 10 bytes -/
structure EndOfDayMessage where
  orig : Alpha 2
  sipTime : BitVec 64
  deriving DecidableEq, Repr

namespace EndOfDayMessage

def encode (message : EndOfDayMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.sipTime)

def decode (bytes : List UInt8) : Option (EndOfDayMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (sipTime, bytes) ← decodeUInt 8 bytes
  pure ({ orig, sipTime }, bytes)

@[simp] theorem encode_length (message : EndOfDayMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : EndOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndOfDayMessage

/-- Sequence Inquiry Response Message: 27 bytes -/
structure SequenceInquiryResponseMessage where
  orig : Alpha 2
  sipTime : BitVec 64
  feedSequence : BitVec 64
  partToken : BitVec 64
  sipState : SipState
  deriving DecidableEq, Repr

namespace SequenceInquiryResponseMessage

def encode (message : SequenceInquiryResponseMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.sipTime
    ++ (encodeUInt 8 message.feedSequence
    ++ (encodeUInt 8 message.partToken
    ++ (SipState.encode message.sipState))))

def decode (bytes : List UInt8) : Option (SequenceInquiryResponseMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (sipTime, bytes) ← decodeUInt 8 bytes
  let (feedSequence, bytes) ← decodeUInt 8 bytes
  let (partToken, bytes) ← decodeUInt 8 bytes
  let (sipState, bytes) ← SipState.decode bytes
  pure ({ orig, sipTime, feedSequence, partToken, sipState }, bytes)

@[simp] theorem encode_length (message : SequenceInquiryResponseMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, SipState.encode_length]

theorem encode_length_pos (message : SequenceInquiryResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceInquiryResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SipState.decode_encode, some_bind]
  rfl

end SequenceInquiryResponseMessage

/-- Symbol State Inquiry Response Message: 30 bytes -/
structure SymbolStateInquiryResponseMessage where
  orig : Alpha 2
  sipTime : BitVec 64
  symbolLong : Alpha 11
  nextTradeId : BitVec 32
  nextActionSequence : BitVec 32
  symbolState : SymbolState
  deriving DecidableEq, Repr

namespace SymbolStateInquiryResponseMessage

def encode (message : SymbolStateInquiryResponseMessage) : List UInt8 :=
  Alpha.encode message.orig
    ++ (encodeUInt 8 message.sipTime
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 4 message.nextTradeId
    ++ (encodeUInt 4 message.nextActionSequence
    ++ (SymbolState.encode message.symbolState)))))

def decode (bytes : List UInt8) : Option (SymbolStateInquiryResponseMessage × List UInt8) := do
  let (orig, bytes) ← Alpha.decode 2 bytes
  let (sipTime, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (nextTradeId, bytes) ← decodeUInt 4 bytes
  let (nextActionSequence, bytes) ← decodeUInt 4 bytes
  let (symbolState, bytes) ← SymbolState.decode bytes
  pure ({ orig, sipTime, symbolLong, nextTradeId, nextActionSequence, symbolState }, bytes)

@[simp] theorem encode_length (message : SymbolStateInquiryResponseMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, SymbolState.encode_length]

theorem encode_length_pos (message : SymbolStateInquiryResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolStateInquiryResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SymbolState.decode_encode, some_bind]
  rfl

end SymbolStateInquiryResponseMessage

/-- Any Return Control Messages Message Payload, selected by Return Control Messages Message Type -/
inductive ReturnControlMessagesMessagePayload where
  | startOfDayMessage (message : StartOfDayMessage) -- "E" 0x45
  | endOfDayMessage (message : EndOfDayMessage) -- "F" 0x46
  | sequenceInquiryResponseMessage (message : SequenceInquiryResponseMessage) -- "C" 0x43
  | symbolStateInquiryResponseMessage (message : SymbolStateInquiryResponseMessage) -- "S" 0x53
  deriving DecidableEq, Repr

namespace ReturnControlMessagesMessagePayload

/-- The Return Control Messages Message Type each message is sent under -/
def tag : ReturnControlMessagesMessagePayload → BitVec 8
  | .startOfDayMessage _ => 69
  | .endOfDayMessage _ => 70
  | .sequenceInquiryResponseMessage _ => 67
  | .symbolStateInquiryResponseMessage _ => 83

def encode : ReturnControlMessagesMessagePayload → List UInt8
  | .startOfDayMessage message => StartOfDayMessage.encode message
  | .endOfDayMessage message => EndOfDayMessage.encode message
  | .sequenceInquiryResponseMessage message => SequenceInquiryResponseMessage.encode message
  | .symbolStateInquiryResponseMessage message => SymbolStateInquiryResponseMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ReturnControlMessagesMessagePayload) : (encode message).length ≤ 30 := by
  cases message with
  | startOfDayMessage inner =>
    simp only [encode, StartOfDayMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [encode, EndOfDayMessage.encode_length]
    omega
  | sequenceInquiryResponseMessage inner =>
    simp only [encode, SequenceInquiryResponseMessage.encode_length]
    omega
  | symbolStateInquiryResponseMessage inner =>
    simp only [encode, SymbolStateInquiryResponseMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ReturnControlMessagesMessagePayload × List UInt8) :=
  if tag = 69 then (StartOfDayMessage.decode bytes).map fun (message, rest) => (.startOfDayMessage message, rest)
  else if tag = 70 then (EndOfDayMessage.decode bytes).map fun (message, rest) => (.endOfDayMessage message, rest)
  else if tag = 67 then (SequenceInquiryResponseMessage.decode bytes).map fun (message, rest) => (.sequenceInquiryResponseMessage message, rest)
  else if tag = 83 then (SymbolStateInquiryResponseMessage.decode bytes).map fun (message, rest) => (.symbolStateInquiryResponseMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ReturnControlMessagesMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ReturnControlMessagesMessagePayload

/-- Return Control Messages Message -/
structure ReturnControlMessagesMessage where
  returnControlMessagesMessagePayload : ReturnControlMessagesMessagePayload
  deriving DecidableEq, Repr

namespace ReturnControlMessagesMessage

def encode (message : ReturnControlMessagesMessage) : List UInt8 :=
  encodeUInt 1 (ReturnControlMessagesMessagePayload.tag message.returnControlMessagesMessagePayload)
    ++ (ReturnControlMessagesMessagePayload.encode message.returnControlMessagesMessagePayload)

def decode (bytes : List UInt8) : Option (ReturnControlMessagesMessage × List UInt8) := do
  let (returnControlMessagesMessageType, bytes) ← decodeUInt 1 bytes
  let (returnControlMessagesMessagePayload, bytes) ← ReturnControlMessagesMessagePayload.decode returnControlMessagesMessageType bytes
  pure ({ returnControlMessagesMessagePayload }, bytes)

theorem encode_length_pos (message : ReturnControlMessagesMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReturnControlMessagesMessage) : (encode message).length ≤ 31 := by
  unfold encode
  cases message.returnControlMessagesMessagePayload with
  | startOfDayMessage inner =>
    simp only [ReturnControlMessagesMessagePayload.encode, List.length_append, encodeUInt_length, StartOfDayMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [ReturnControlMessagesMessagePayload.encode, List.length_append, encodeUInt_length, EndOfDayMessage.encode_length]
    omega
  | sequenceInquiryResponseMessage inner =>
    simp only [ReturnControlMessagesMessagePayload.encode, List.length_append, encodeUInt_length, SequenceInquiryResponseMessage.encode_length]
    omega
  | symbolStateInquiryResponseMessage inner =>
    simp only [ReturnControlMessagesMessagePayload.encode, List.length_append, encodeUInt_length, SymbolStateInquiryResponseMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ReturnControlMessagesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ReturnControlMessagesMessagePayload.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ReturnControlMessagesMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ReturnControlMessagesMessage

/-- Any Category Payload, selected by Message Category -/
inductive CategoryPayload where
  | inboundQuoteMessagesMessage (message : InboundQuoteMessagesMessage) -- "Q" 0x51
  | inboundTradeMessagesMessage (message : InboundTradeMessagesMessage) -- "T" 0x54
  | inboundAdministrativeMessagesMessage (message : InboundAdministrativeMessagesMessage) -- "A" 0x41
  | inboundControlMessagesMessage (message : InboundControlMessagesMessage) -- "C" 0x43
  | returnAdministrativeMessagesMessage (message : ReturnAdministrativeMessagesMessage) -- "a" 0x61
  | returnControlMessagesMessage (message : ReturnControlMessagesMessage) -- "c" 0x63
  deriving DecidableEq, Repr

namespace CategoryPayload

/-- The Message Category each message is sent under -/
def tag : CategoryPayload → BitVec 8
  | .inboundQuoteMessagesMessage _ => 81
  | .inboundTradeMessagesMessage _ => 84
  | .inboundAdministrativeMessagesMessage _ => 65
  | .inboundControlMessagesMessage _ => 67
  | .returnAdministrativeMessagesMessage _ => 97
  | .returnControlMessagesMessage _ => 99

def encode : CategoryPayload → List UInt8
  | .inboundQuoteMessagesMessage message => InboundQuoteMessagesMessage.encode message
  | .inboundTradeMessagesMessage message => InboundTradeMessagesMessage.encode message
  | .inboundAdministrativeMessagesMessage message => InboundAdministrativeMessagesMessage.encode message
  | .inboundControlMessagesMessage message => InboundControlMessagesMessage.encode message
  | .returnAdministrativeMessagesMessage message => ReturnAdministrativeMessagesMessage.encode message
  | .returnControlMessagesMessage message => ReturnControlMessagesMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : CategoryPayload) : (encode message).length ≤ 1835093 := by
  cases message with
  | inboundQuoteMessagesMessage inner =>
    have bound_inner := InboundQuoteMessagesMessage.encode_length_le inner
    simp only [encode]
    omega
  | inboundTradeMessagesMessage inner =>
    have bound_inner := InboundTradeMessagesMessage.encode_length_le inner
    simp only [encode]
    omega
  | inboundAdministrativeMessagesMessage inner =>
    have bound_inner := InboundAdministrativeMessagesMessage.encode_length_le inner
    simp only [encode]
    omega
  | inboundControlMessagesMessage inner =>
    have bound_inner := InboundControlMessagesMessage.encode_length_le inner
    simp only [encode]
    omega
  | returnAdministrativeMessagesMessage inner =>
    have bound_inner := ReturnAdministrativeMessagesMessage.encode_length_le inner
    simp only [encode]
    omega
  | returnControlMessagesMessage inner =>
    have bound_inner := ReturnControlMessagesMessage.encode_length_le inner
    simp only [encode]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option CategoryPayload :=
  if tag = 81 then (InboundQuoteMessagesMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inboundQuoteMessagesMessage message) else none
  else if tag = 84 then (InboundTradeMessagesMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inboundTradeMessagesMessage message) else none
  else if tag = 65 then (InboundAdministrativeMessagesMessage.decode bytes).map fun message => .inboundAdministrativeMessagesMessage message
  else if tag = 67 then (InboundControlMessagesMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inboundControlMessagesMessage message) else none
  else if tag = 97 then (ReturnAdministrativeMessagesMessage.decode bytes).map fun message => .returnAdministrativeMessagesMessage message
  else if tag = 99 then (ReturnControlMessagesMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.returnControlMessagesMessage message) else none
  else none

theorem decode_encode (message : CategoryPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | inboundQuoteMessagesMessage message => simp [decode, encode, tag, InboundQuoteMessagesMessage.decode_encode_nil]
  | inboundTradeMessagesMessage message => simp [decode, encode, tag, InboundTradeMessagesMessage.decode_encode_nil]
  | inboundAdministrativeMessagesMessage message => simp [decode, encode, tag, InboundAdministrativeMessagesMessage.decode_encode]
  | inboundControlMessagesMessage message => simp [decode, encode, tag, InboundControlMessagesMessage.decode_encode_nil]
  | returnAdministrativeMessagesMessage message => simp [decode, encode, tag, ReturnAdministrativeMessagesMessage.decode_encode]
  | returnControlMessagesMessage message => simp [decode, encode, tag, ReturnControlMessagesMessage.decode_encode_nil]

end CategoryPayload

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  version : BitVec 8
  categoryPayload : CategoryPayload
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 message.version
    ++ (encodeUInt 1 (CategoryPayload.tag message.categoryPayload)
    ++ (CategoryPayload.encode message.categoryPayload))

def decode (bytes : List UInt8) : Option SequencedDataPacket := do
  let (version, bytes) ← decodeUInt 1 bytes
  let (messageCategory, bytes) ← decodeUInt 1 bytes
  let categoryPayload ← CategoryPayload.decode messageCategory bytes
  pure { version, categoryPayload }

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 1835095 := by
  unfold encode
  cases message.categoryPayload with
  | inboundQuoteMessagesMessage inner =>
    have bound_inner := InboundQuoteMessagesMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | inboundTradeMessagesMessage inner =>
    have bound_inner := InboundTradeMessagesMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | inboundAdministrativeMessagesMessage inner =>
    have bound_inner := InboundAdministrativeMessagesMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | inboundControlMessagesMessage inner =>
    have bound_inner := InboundControlMessagesMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | returnAdministrativeMessagesMessage inner =>
    have bound_inner := ReturnAdministrativeMessagesMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | returnControlMessagesMessage inner =>
    have bound_inner := ReturnControlMessagesMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega

theorem decode_encode (message : SequencedDataPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CategoryPayload.decode_encode, some_bind]
  rfl

end SequencedDataPacket

/-- Debug Packet -/
structure DebugPacket where
  text : Capped 65535
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  message.text.val

def decode (bytes : List UInt8) : Option DebugPacket := do
  let text_ := bytes
  if fits_text : text_.length ≤ 65535 then
    pure { text := ⟨text_, fits_text⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DebugPacket) : (encode message).length ≤ 65535 := by
  have bound_text := message.text.length_le
  unfold encode
  omega

theorem decode_encode (message : DebugPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.text.length_le]
  rfl

end DebugPacket

/-- Login Accepted Packet: 30 bytes -/
structure LoginAcceptedPacket where
  acceptedSession : Alpha 10
  acceptedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.acceptedSession
    ++ (Alpha.encode message.acceptedSequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (acceptedSession, bytes) ← Alpha.decode 10 bytes
  let (acceptedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ acceptedSession, acceptedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginAcceptedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  Alpha.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← Alpha.decode 1 bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRejectedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRejectedPacket

/-- Server Heartbeat Packet: 0 bytes -/
structure ServerHeartbeatPacket where
  deriving DecidableEq, Repr

namespace ServerHeartbeatPacket

def encode (_ : ServerHeartbeatPacket) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeatPacket × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeatPacket) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeatPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServerHeartbeatPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServerHeartbeatPacket

/-- End Of Session Packet: 0 bytes -/
structure EndOfSessionPacket where
  deriving DecidableEq, Repr

namespace EndOfSessionPacket

def encode (_ : EndOfSessionPacket) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSessionPacket × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSessionPacket) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSessionPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfSessionPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EndOfSessionPacket

/-- Any Server Tcp Payload, selected by Server Packet Type -/
inductive ServerTcpPayload where
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | serverHeartbeatPacket (message : ServerHeartbeatPacket) -- "H" 0x48
  | endOfSessionPacket (message : EndOfSessionPacket) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace ServerTcpPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerTcpPayload → BitVec 8
  | .sequencedDataPacket _ => 83
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .serverHeartbeatPacket _ => 72
  | .endOfSessionPacket _ => 90

def encode : ServerTcpPayload → List UInt8
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .serverHeartbeatPacket message => ServerHeartbeatPacket.encode message
  | .endOfSessionPacket message => EndOfSessionPacket.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerTcpPayload) : (encode message).length ≤ 1835095 := by
  cases message with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [encode]
    omega
  | loginAcceptedPacket inner =>
    simp only [encode, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [encode, LoginRejectedPacket.encode_length]
    omega
  | serverHeartbeatPacket inner =>
    simp only [encode, ServerHeartbeatPacket.encode_length]
    omega
  | endOfSessionPacket inner =>
    simp only [encode, EndOfSessionPacket.encode_length]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ServerTcpPayload :=
  if tag = 83 then (SequencedDataPacket.decode bytes).map fun message => .sequencedDataPacket message
  else if tag = 43 then (DebugPacket.decode bytes).map fun message => .debugPacket message
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginAcceptedPacket message) else none
  else if tag = 74 then (LoginRejectedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRejectedPacket message) else none
  else if tag = 72 then (ServerHeartbeatPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeatPacket message) else none
  else if tag = 90 then (EndOfSessionPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfSessionPacket message) else none
  else none

theorem decode_encode (message : ServerTcpPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode]
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode]
  | loginAcceptedPacket message => simp [decode, encode, tag, LoginAcceptedPacket.decode_encode_nil]
  | loginRejectedPacket message => simp [decode, encode, tag, LoginRejectedPacket.decode_encode_nil]
  | serverHeartbeatPacket message => simp [decode, encode, tag, ServerHeartbeatPacket.decode_encode_nil]
  | endOfSessionPacket message => simp [decode, encode, tag, EndOfSessionPacket.decode_encode_nil]

end ServerTcpPayload

/-- Server Packet: the body, which the record carries with the proof it fits its frame -/
structure ServerPacketBody where
  serverTcpPayload : ServerTcpPayload
  deriving DecidableEq, Repr

namespace ServerPacketBody

def encodeBody (message : ServerPacketBody) : List UInt8 :=
  encodeUInt 1 (ServerTcpPayload.tag message.serverTcpPayload)
    ++ (ServerTcpPayload.encode message.serverTcpPayload)

def decodeBody (bytes : List UInt8) : Option ServerPacketBody := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let serverTcpPayload ← ServerTcpPayload.decode serverPacketType bytes
  pure { serverTcpPayload }

theorem decodeBody_encodeBody (message : ServerPacketBody) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerTcpPayload.decode_encode, some_bind]
  rfl

end ServerPacketBody

/-- Server Packet: the body with the proof its encoding fits Packet Length, whose 2 bytes no bound of the fields fits -/
abbrev ServerPacket := Fitting ServerPacketBody.encodeBody 0 65536

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeFramed 2 0 ServerPacketBody.encodeBody message.val

def decode : List UInt8 → Option (ServerPacket × List UInt8) :=
  decodeFittingAll 2 0 ServerPacketBody.encodeBody ServerPacketBody.decodeBody

@[simp] theorem decode_encode (message : ServerPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAll_encodeFramed 2 0 ServerPacketBody.encodeBody ServerPacketBody.decodeBody message (ServerPacketBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : ServerPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : ServerPacket) : (encode message).length ≤ 65537 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramed_length]
  omega

end ServerPacket

end Omi.NasdaqUtpInputUtpV40Server
