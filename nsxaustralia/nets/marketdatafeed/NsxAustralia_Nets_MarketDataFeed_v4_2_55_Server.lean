import Wire

/-!
# Nation Stock Exchange of Australia NSX Market Data Feed v4.2.55

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NsxaustraliaNetsMarketdatafeedItchV4255Server

/-- Reject Reason Code: one byte code -/
def RejectReasonCode.codes : List UInt8 :=
  [0x41, 0x53]

inductive RejectReasonCode where
  | notAuthorized -- Not Authorized
  | sessionNotAvailable -- Session Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectReasonCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectReasonCode

def toByte : RejectReasonCode → UInt8
  | .notAuthorized => 0x41
  | .sessionNotAvailable => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectReasonCode :=
  if byte = 0x41 then .notAuthorized
  else .sessionNotAvailable

def ofByte (byte : UInt8) : RejectReasonCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectReasonCode) : ofByte value.toByte = value := by
  cases value with
  | notAuthorized => decide
  | sessionNotAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RejectReasonCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RejectReasonCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RejectReasonCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RejectReasonCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RejectReasonCode

/-- Event Status: one byte code -/
def EventStatus.codes : List UInt8 :=
  [0x53, 0x43, 0x54]

inductive EventStatus where
  | scheduled -- Scheduled
  | canceled -- Canceled
  | triggered -- Triggered
  | unlisted (byte : { byte : UInt8 // byte ∉ EventStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventStatus

def toByte : EventStatus → UInt8
  | .scheduled => 0x53
  | .canceled => 0x43
  | .triggered => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventStatus :=
  if byte = 0x53 then .scheduled
  else if byte = 0x43 then .canceled
  else .triggered

def ofByte (byte : UInt8) : EventStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventStatus) : ofByte value.toByte = value := by
  cases value with
  | scheduled => decide
  | canceled => decide
  | triggered => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventStatus

/-- Asset Type: one byte code -/
def AssetType.codes : List UInt8 :=
  [0x44, 0x45, 0x49]

inductive AssetType where
  | debt -- Debt
  | equity -- Equity
  | index -- Index
  | unlisted (byte : { byte : UInt8 // byte ∉ AssetType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AssetType

def toByte : AssetType → UInt8
  | .debt => 0x44
  | .equity => 0x45
  | .index => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AssetType :=
  if byte = 0x44 then .debt
  else if byte = 0x45 then .equity
  else .index

def ofByte (byte : UInt8) : AssetType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AssetType) : ofByte value.toByte = value := by
  cases value with
  | debt => decide
  | equity => decide
  | index => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AssetType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AssetType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AssetType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AssetType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AssetType

/-- Trading State: one byte code -/
def TradingState.codes : List UInt8 :=
  [0x54, 0x56]

inductive TradingState where
  | normalTrading -- Normal Trading
  | suspended -- Suspended
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .normalTrading => 0x54
  | .suspended => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x54 then .normalTrading
  else .suspended

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | normalTrading => decide
  | suspended => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingState

/-- Reason: one byte code -/
def Reason.codes : List UInt8 :=
  [0x4E, 0x48, 0x53]

inductive Reason where
  | normalTrading -- Normal Trading
  | haltedDueToExtremeTradeRange -- Halted Due To Extreme Trade Range
  | supervisory -- Supervisory
  | unlisted (byte : { byte : UInt8 // byte ∉ Reason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reason

def toByte : Reason → UInt8
  | .normalTrading => 0x4E
  | .haltedDueToExtremeTradeRange => 0x48
  | .supervisory => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reason :=
  if byte = 0x4E then .normalTrading
  else if byte = 0x48 then .haltedDueToExtremeTradeRange
  else .supervisory

def ofByte (byte : UInt8) : Reason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reason) : ofByte value.toByte = value := by
  cases value with
  | normalTrading => decide
  | haltedDueToExtremeTradeRange => decide
  | supervisory => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Reason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Reason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Reason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Reason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Reason

/-- Attribute Type: one byte code -/
def AttributeType.codes : List UInt8 :=
  [0x52, 0x43, 0x44, 0x64, 0x50, 0x70, 0x41, 0x42]

inductive AttributeType where
  | previousDayClose -- Previous Day Close
  | closePrice -- Close Price
  | etrUpperLimitPercentage -- Etr Upper Limit Percentage
  | etrLowerLimitPercentage -- Etr Lower Limit Percentage
  | aotUpperLimitPercentage -- Aot Upper Limit Percentage
  | aotLowerLimitPercentage -- Aot Lower Limit Percentage
  | aotReferencePrice -- Aot Reference Price
  | etrReferencePrice -- Etr Reference Price
  | unlisted (byte : { byte : UInt8 // byte ∉ AttributeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AttributeType

def toByte : AttributeType → UInt8
  | .previousDayClose => 0x52
  | .closePrice => 0x43
  | .etrUpperLimitPercentage => 0x44
  | .etrLowerLimitPercentage => 0x64
  | .aotUpperLimitPercentage => 0x50
  | .aotLowerLimitPercentage => 0x70
  | .aotReferencePrice => 0x41
  | .etrReferencePrice => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AttributeType :=
  if byte = 0x52 then .previousDayClose
  else if byte = 0x43 then .closePrice
  else if byte = 0x44 then .etrUpperLimitPercentage
  else if byte = 0x64 then .etrLowerLimitPercentage
  else if byte = 0x50 then .aotUpperLimitPercentage
  else if byte = 0x70 then .aotLowerLimitPercentage
  else if byte = 0x41 then .aotReferencePrice
  else .etrReferencePrice

def ofByte (byte : UInt8) : AttributeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AttributeType) : ofByte value.toByte = value := by
  cases value with
  | previousDayClose => decide
  | closePrice => decide
  | etrUpperLimitPercentage => decide
  | etrLowerLimitPercentage => decide
  | aotUpperLimitPercentage => decide
  | aotLowerLimitPercentage => decide
  | aotReferencePrice => decide
  | etrReferencePrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AttributeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AttributeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AttributeType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AttributeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AttributeType

/-- Order Verb: one byte code -/
def OrderVerb.codes : List UInt8 :=
  [0x42, 0x53]

inductive OrderVerb where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderVerb.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderVerb

def toByte : OrderVerb → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderVerb :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : OrderVerb :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderVerb) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderVerb) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderVerb × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderVerb) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderVerb) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderVerb

/-- Printable: one byte code -/
def Printable.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Printable where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ Printable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Printable

def toByte : Printable → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Printable :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : Printable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Printable) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Printable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Printable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Printable) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Printable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Printable

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x4F, 0x49, 0x43]

inductive CrossType where
  | openingAuction -- Opening Auction
  | intradayAuction -- Intraday Auction
  | closingAuction -- Closing Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .openingAuction => 0x4F
  | .intradayAuction => 0x49
  | .closingAuction => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4F then .openingAuction
  else if byte = 0x49 then .intradayAuction
  else .closingAuction

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | openingAuction => decide
  | intradayAuction => decide
  | closingAuction => decide
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

/-- Trade Indicator: one byte code -/
def TradeIndicator.codes : List UInt8 :=
  [0x42]

inductive TradeIndicator where
  | blockSpecial -- Block Special
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeIndicator

def toByte : TradeIndicator → UInt8
  | .blockSpecial => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : TradeIndicator :=
  .blockSpecial

def ofByte (byte : UInt8) : TradeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeIndicator) : ofByte value.toByte = value := by
  cases value with
  | blockSpecial => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeIndicator

/-- Trade Source: one byte code -/
def TradeSource.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x49, 0x4B, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x55, 0x56, 0x58, 0x59, 0x5A]

inductive TradeSource where
  | autotrade -- Autotrade
  | bestExecution -- Best Execution
  | offMarketAutomaticCrossing -- Off Market Automatic Crossing
  | directedReportingOrOffMarketTradesCrossing -- Directed Reporting Or Off Market Trades Crossing
  | specialCrossingLessThanAMarketableParcel -- Special Crossing Less Than A Marketable Parcel
  | forwardDelivery -- Forward Delivery
  | approvedIndexCrossing -- Approved Index Crossing
  | buyBackSales -- Buy Back Sales
  | marriageCrossing -- Marriage Crossing
  | tradesIncludingCrossingsOutsideOfMarketHours -- Trades Including Crossings Outside Of Market Hours
  | foreignResidentsOrRecognisedOverseasExchange -- Foreign Residents Or Recognised Overseas Exchange
  | blockSpecialCrossingOrLoanSecurities -- Block Special Crossing Or Loan Securities
  | specialCrossingLessThanAMarketableParcel_51 -- Special Crossing Less Than A Marketable Parcel
  | strategy -- Strategy
  | shortSales -- Short Sales
  | forForeignToForeignSecurities -- For Foreign To Foreign Securities
  | bookValueSwitchSales -- Book Value Switch Sales
  | portfolioSpecialCrossing -- Portfolio Special Crossing
  | special -- Special
  | specialCrossingUnderwritingDisposalOrExchangeApproval -- Special Crossing Underwriting Disposal Or Exchange Approval
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeSource.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeSource

def toByte : TradeSource → UInt8
  | .autotrade => 0x41
  | .bestExecution => 0x42
  | .offMarketAutomaticCrossing => 0x43
  | .directedReportingOrOffMarketTradesCrossing => 0x44
  | .specialCrossingLessThanAMarketableParcel => 0x45
  | .forwardDelivery => 0x46
  | .approvedIndexCrossing => 0x49
  | .buyBackSales => 0x4B
  | .marriageCrossing => 0x4D
  | .tradesIncludingCrossingsOutsideOfMarketHours => 0x4E
  | .foreignResidentsOrRecognisedOverseasExchange => 0x4F
  | .blockSpecialCrossingOrLoanSecurities => 0x50
  | .specialCrossingLessThanAMarketableParcel_51 => 0x51
  | .strategy => 0x52
  | .shortSales => 0x53
  | .forForeignToForeignSecurities => 0x55
  | .bookValueSwitchSales => 0x56
  | .portfolioSpecialCrossing => 0x58
  | .special => 0x59
  | .specialCrossingUnderwritingDisposalOrExchangeApproval => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeSource :=
  if byte = 0x41 then .autotrade
  else if byte = 0x42 then .bestExecution
  else if byte = 0x43 then .offMarketAutomaticCrossing
  else if byte = 0x44 then .directedReportingOrOffMarketTradesCrossing
  else if byte = 0x45 then .specialCrossingLessThanAMarketableParcel
  else if byte = 0x46 then .forwardDelivery
  else if byte = 0x49 then .approvedIndexCrossing
  else if byte = 0x4B then .buyBackSales
  else if byte = 0x4D then .marriageCrossing
  else if byte = 0x4E then .tradesIncludingCrossingsOutsideOfMarketHours
  else if byte = 0x4F then .foreignResidentsOrRecognisedOverseasExchange
  else if byte = 0x50 then .blockSpecialCrossingOrLoanSecurities
  else if byte = 0x51 then .specialCrossingLessThanAMarketableParcel_51
  else if byte = 0x52 then .strategy
  else if byte = 0x53 then .shortSales
  else if byte = 0x55 then .forForeignToForeignSecurities
  else if byte = 0x56 then .bookValueSwitchSales
  else if byte = 0x58 then .portfolioSpecialCrossing
  else if byte = 0x59 then .special
  else .specialCrossingUnderwritingDisposalOrExchangeApproval

def ofByte (byte : UInt8) : TradeSource :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeSource) : ofByte value.toByte = value := by
  cases value with
  | autotrade => decide
  | bestExecution => decide
  | offMarketAutomaticCrossing => decide
  | directedReportingOrOffMarketTradesCrossing => decide
  | specialCrossingLessThanAMarketableParcel => decide
  | forwardDelivery => decide
  | approvedIndexCrossing => decide
  | buyBackSales => decide
  | marriageCrossing => decide
  | tradesIncludingCrossingsOutsideOfMarketHours => decide
  | foreignResidentsOrRecognisedOverseasExchange => decide
  | blockSpecialCrossingOrLoanSecurities => decide
  | specialCrossingLessThanAMarketableParcel_51 => decide
  | strategy => decide
  | shortSales => decide
  | forForeignToForeignSecurities => decide
  | bookValueSwitchSales => decide
  | portfolioSpecialCrossing => decide
  | special => decide
  | specialCrossingUnderwritingDisposalOrExchangeApproval => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeSource) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeSource × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeSource) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeSource) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeSource

/-- Debug Packet -/
structure DebugPacket where
  debugText : Capped 64642
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  message.debugText.val

def decode (bytes : List UInt8) : Option DebugPacket := do
  let debugText_ := bytes
  if fits_debugText : debugText_.length ≤ 64642 then
    pure { debugText := ⟨debugText_, fits_debugText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DebugPacket) : (encode message).length ≤ 64642 := by
  have bound_debugText := message.debugText.length_le
  unfold encode
  omega

theorem decode_encode (message : DebugPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.debugText.length_le]
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
  rejectReasonCode : RejectReasonCode
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  RejectReasonCode.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← RejectReasonCode.decode bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [RejectReasonCode.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RejectReasonCode.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRejectedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRejectedPacket

/-- Timestamp Message: 8 bytes -/
structure TimestampMessage where
  nanosecond : BitVec 64
  deriving DecidableEq, Repr

namespace TimestampMessage

def encode (message : TimestampMessage) : List UInt8 :=
  encodeUInt 8 message.nanosecond

def decode (bytes : List UInt8) : Option (TimestampMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUInt 8 bytes
  pure ({ nanosecond }, bytes)

@[simp] theorem encode_length (message : TimestampMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : TimestampMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimestampMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TimestampMessage

/-- System Event Message: 61 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 32
  group : Alpha 20
  product : Alpha 12
  orderbook : BitVec 32
  eventCode : Alpha 12
  eventStatus : EventStatus
  scheduledTime : BitVec 64
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.product
    ++ (encodeUInt 4 message.orderbook
    ++ (Alpha.encode message.eventCode
    ++ (EventStatus.encode message.eventStatus
    ++ (encodeUInt 8 message.scheduledTime))))))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (group, bytes) ← Alpha.decode 20 bytes
  let (product, bytes) ← Alpha.decode 12 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← Alpha.decode 12 bytes
  let (eventStatus, bytes) ← EventStatus.decode bytes
  let (scheduledTime, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, group, product, orderbook, eventCode, eventStatus, scheduledTime }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, EventStatus.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, EventStatus.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Price Tick Size Message: 24 bytes -/
structure PriceTickSizeMessage where
  timestamp : BitVec 32
  tickSizeTableId : BitVec 32
  tickSize : BitVec 64
  priceStart : BitVec 64
  deriving DecidableEq, Repr

namespace PriceTickSizeMessage

def encode (message : PriceTickSizeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.tickSizeTableId
    ++ (encodeUInt 8 message.tickSize
    ++ (encodeUInt 8 message.priceStart)))

def decode (bytes : List UInt8) : Option (PriceTickSizeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (tickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (tickSize, bytes) ← decodeUInt 8 bytes
  let (priceStart, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, tickSizeTableId, tickSize, priceStart }, bytes)

@[simp] theorem encode_length (message : PriceTickSizeMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PriceTickSizeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceTickSizeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriceTickSizeMessage

/-- Quantity Tick Size Message: 24 bytes -/
structure QuantityTickSizeMessage where
  timestamp : BitVec 32
  tickSizeTableId : BitVec 32
  tickSize : BitVec 64
  quantityStart : BitVec 64
  deriving DecidableEq, Repr

namespace QuantityTickSizeMessage

def encode (message : QuantityTickSizeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.tickSizeTableId
    ++ (encodeUInt 8 message.tickSize
    ++ (encodeUInt 8 message.quantityStart)))

def decode (bytes : List UInt8) : Option (QuantityTickSizeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (tickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (tickSize, bytes) ← decodeUInt 8 bytes
  let (quantityStart, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, tickSizeTableId, tickSize, quantityStart }, bytes)

@[simp] theorem encode_length (message : QuantityTickSizeMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : QuantityTickSizeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuantityTickSizeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuantityTickSizeMessage

/-- Orderbook Directory Message: 320 bytes -/
structure OrderbookDirectoryMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  isin : Alpha 12
  securityCode : Alpha 100
  securityName : Alpha 100
  currency : Alpha 3
  board : Alpha 20
  product : Alpha 12
  minimumQuantity : BitVec 64
  quantityTickSizeTableId : BitVec 32
  quantityDecimals : BitVec 32
  priceTickSizeTableId : BitVec 32
  priceDecimals : BitVec 32
  listing : BitVec 64
  expiry : BitVec 64
  assetType : AssetType
  settleDate : BitVec 32
  referenceAlpha12 : Alpha 12
  remarks : Alpha 8
  deriving DecidableEq, Repr

namespace OrderbookDirectoryMessage

def encode (message : OrderbookDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.securityCode
    ++ (Alpha.encode message.securityName
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.board
    ++ (Alpha.encode message.product
    ++ (encodeUInt 8 message.minimumQuantity
    ++ (encodeUInt 4 message.quantityTickSizeTableId
    ++ (encodeUInt 4 message.quantityDecimals
    ++ (encodeUInt 4 message.priceTickSizeTableId
    ++ (encodeUInt 4 message.priceDecimals
    ++ (encodeUInt 8 message.listing
    ++ (encodeUInt 8 message.expiry
    ++ (AssetType.encode message.assetType
    ++ (encodeUInt 4 message.settleDate
    ++ (Alpha.encode message.referenceAlpha12
    ++ (Alpha.encode message.remarks))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderbookDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (securityCode, bytes) ← Alpha.decode 100 bytes
  let (securityName, bytes) ← Alpha.decode 100 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (board, bytes) ← Alpha.decode 20 bytes
  let (product, bytes) ← Alpha.decode 12 bytes
  let (minimumQuantity, bytes) ← decodeUInt 8 bytes
  let (quantityTickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (quantityDecimals, bytes) ← decodeUInt 4 bytes
  let (priceTickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (priceDecimals, bytes) ← decodeUInt 4 bytes
  let (listing, bytes) ← decodeUInt 8 bytes
  let (expiry, bytes) ← decodeUInt 8 bytes
  let (assetType, bytes) ← AssetType.decode bytes
  let (settleDate, bytes) ← decodeUInt 4 bytes
  let (referenceAlpha12, bytes) ← Alpha.decode 12 bytes
  let (remarks, bytes) ← Alpha.decode 8 bytes
  pure ({ timestamp, orderbook, isin, securityCode, securityName, currency, board, product, minimumQuantity, quantityTickSizeTableId, quantityDecimals, priceTickSizeTableId, priceDecimals, listing, expiry, assetType, settleDate, referenceAlpha12, remarks }, bytes)

@[simp] theorem encode_length (message : OrderbookDirectoryMessage) : (encode message).length = 320 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, AssetType.encode_length]

theorem encode_length_pos (message : OrderbookDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, AssetType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderbookDirectoryMessage

/-- Orderbook Trading Action Message: 10 bytes -/
structure OrderbookTradingActionMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  tradingState : TradingState
  reason : Reason
  deriving DecidableEq, Repr

namespace OrderbookTradingActionMessage

def encode (message : OrderbookTradingActionMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (TradingState.encode message.tradingState
    ++ (Reason.encode message.reason)))

def decode (bytes : List UInt8) : Option (OrderbookTradingActionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ timestamp, orderbook, tradingState, reason }, bytes)

@[simp] theorem encode_length (message : OrderbookTradingActionMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradingState.encode_length, Reason.encode_length]

theorem encode_length_pos (message : OrderbookTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradingState.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end OrderbookTradingActionMessage

/-- Orderbook Attribute Message: 18 bytes -/
structure OrderbookAttributeMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  attributeValue : BitVec 64
  attributeType : AttributeType
  reason : Reason
  deriving DecidableEq, Repr

namespace OrderbookAttributeMessage

def encode (message : OrderbookAttributeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 8 message.attributeValue
    ++ (AttributeType.encode message.attributeType
    ++ (Reason.encode message.reason))))

def decode (bytes : List UInt8) : Option (OrderbookAttributeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (attributeValue, bytes) ← decodeUInt 8 bytes
  let (attributeType, bytes) ← AttributeType.decode bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ timestamp, orderbook, attributeValue, attributeType, reason }, bytes)

@[simp] theorem encode_length (message : OrderbookAttributeMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, AttributeType.encode_length, Reason.encode_length]

theorem encode_length_pos (message : OrderbookAttributeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookAttributeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AttributeType.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end OrderbookAttributeMessage

/-- Firm Directory Message: 38 bytes -/
structure FirmDirectoryMessage where
  timestamp : BitVec 32
  firmId : BitVec 32
  firmCode : Alpha 30
  deriving DecidableEq, Repr

namespace FirmDirectoryMessage

def encode (message : FirmDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.firmId
    ++ (Alpha.encode message.firmCode))

def decode (bytes : List UInt8) : Option (FirmDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (firmId, bytes) ← decodeUInt 4 bytes
  let (firmCode, bytes) ← Alpha.decode 30 bytes
  pure ({ timestamp, firmId, firmCode }, bytes)

@[simp] theorem encode_length (message : FirmDirectoryMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : FirmDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FirmDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FirmDirectoryMessage

/-- Add Order Message: 37 bytes -/
structure AddOrderMessage where
  timestamp : BitVec 32
  orderNumber : BitVec 64
  orderVerb : OrderVerb
  quantity : BitVec 64
  orderbook : BitVec 32
  price : BitVec 64
  firmId : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.orderNumber
    ++ (OrderVerb.encode message.orderVerb
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.firmId))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (orderVerb, bytes) ← OrderVerb.decode bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (firmId, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, orderNumber, orderVerb, quantity, orderbook, price, firmId }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OrderVerb.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderVerb.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessage

/-- Order Executed Message: 33 bytes -/
structure OrderExecutedMessage where
  timestamp : BitVec 32
  orderNumber : BitVec 64
  executedQuantity : BitVec 64
  matchNumber : BitVec 64
  printable : Printable
  aggressorFirmId : BitVec 32
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 8 message.matchNumber
    ++ (Printable.encode message.printable
    ++ (encodeUInt 4 message.aggressorFirmId)))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (printable, bytes) ← Printable.decode bytes
  let (aggressorFirmId, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, orderNumber, executedQuantity, matchNumber, printable, aggressorFirmId }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Executed With Price Message: 37 bytes -/
structure OrderExecutedWithPriceMessage where
  timestamp : BitVec 32
  orderNumber : BitVec 64
  executedQuantity : BitVec 64
  matchNumber : BitVec 64
  printable : Printable
  executionPrice : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 8 message.matchNumber
    ++ (Printable.encode message.printable
    ++ (encodeUInt 8 message.executionPrice)))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (printable, bytes) ← Printable.decode bytes
  let (executionPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, orderNumber, executedQuantity, matchNumber, printable, executionPrice }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length]

theorem encode_length_pos (message : OrderExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedWithPriceMessage

/-- Broken Trade Message: 13 bytes -/
structure BrokenTradeMessage where
  timestamp : BitVec 32
  matchNumber : BitVec 64
  reason : Reason
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.matchNumber
    ++ (Reason.encode message.reason))

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ timestamp, matchNumber, reason }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Reason.encode_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end BrokenTradeMessage

/-- Order Delete Message: 12 bytes -/
structure OrderDeleteMessage where
  timestamp : BitVec 32
  orderNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.orderNumber)

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, orderNumber }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDeleteMessage

/-- Order Replace Message: 36 bytes -/
structure OrderReplaceMessage where
  timestamp : BitVec 32
  originalOrderNumber : BitVec 64
  newOrderNumber : BitVec 64
  quantity : BitVec 64
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderReplaceMessage

def encode (message : OrderReplaceMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.originalOrderNumber
    ++ (encodeUInt 8 message.newOrderNumber
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 8 message.price))))

def decode (bytes : List UInt8) : Option (OrderReplaceMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (originalOrderNumber, bytes) ← decodeUInt 8 bytes
  let (newOrderNumber, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, originalOrderNumber, newOrderNumber, quantity, price }, bytes)

@[simp] theorem encode_length (message : OrderReplaceMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderReplaceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end OrderReplaceMessage

/-- Indicative Price Quantity Message: 57 bytes -/
structure IndicativePriceQuantityMessage where
  timestamp : BitVec 32
  theoreticalOpeningQuantity : BitVec 64
  orderbook : BitVec 32
  bestBid : BitVec 64
  bestOffer : BitVec 64
  theoreticalOpeningPrice : BitVec 64
  crossType : CrossType
  bestBidSize : BitVec 64
  bestOfferSize : BitVec 64
  deriving DecidableEq, Repr

namespace IndicativePriceQuantityMessage

def encode (message : IndicativePriceQuantityMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.theoreticalOpeningQuantity
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 8 message.bestBid
    ++ (encodeUInt 8 message.bestOffer
    ++ (encodeUInt 8 message.theoreticalOpeningPrice
    ++ (CrossType.encode message.crossType
    ++ (encodeUInt 8 message.bestBidSize
    ++ (encodeUInt 8 message.bestOfferSize))))))))

def decode (bytes : List UInt8) : Option (IndicativePriceQuantityMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (theoreticalOpeningQuantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (bestBid, bytes) ← decodeUInt 8 bytes
  let (bestOffer, bytes) ← decodeUInt 8 bytes
  let (theoreticalOpeningPrice, bytes) ← decodeUInt 8 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (bestBidSize, bytes) ← decodeUInt 8 bytes
  let (bestOfferSize, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, theoreticalOpeningQuantity, orderbook, bestBid, bestOffer, theoreticalOpeningPrice, crossType, bestBidSize, bestOfferSize }, bytes)

@[simp] theorem encode_length (message : IndicativePriceQuantityMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CrossType.encode_length]

theorem encode_length_pos (message : IndicativePriceQuantityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicativePriceQuantityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndicativePriceQuantityMessage

/-- Trade Message: 43 bytes -/
structure TradeMessage where
  timestamp : BitVec 32
  executedQuantity : BitVec 64
  orderbook : BitVec 32
  printable : Printable
  executionPrice : BitVec 64
  matchNumber : BitVec 64
  tradeIndicator : TradeIndicator
  buyFirmId : BitVec 32
  sellFirmId : BitVec 32
  tradeSource : TradeSource
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 4 message.orderbook
    ++ (Printable.encode message.printable
    ++ (encodeUInt 8 message.executionPrice
    ++ (encodeUInt 8 message.matchNumber
    ++ (TradeIndicator.encode message.tradeIndicator
    ++ (encodeUInt 4 message.buyFirmId
    ++ (encodeUInt 4 message.sellFirmId
    ++ (TradeSource.encode message.tradeSource)))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (printable, bytes) ← Printable.decode bytes
  let (executionPrice, bytes) ← decodeUInt 8 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (tradeIndicator, bytes) ← TradeIndicator.decode bytes
  let (buyFirmId, bytes) ← decodeUInt 4 bytes
  let (sellFirmId, bytes) ← decodeUInt 4 bytes
  let (tradeSource, bytes) ← TradeSource.decode bytes
  pure ({ timestamp, executedQuantity, orderbook, printable, executionPrice, matchNumber, tradeIndicator, buyFirmId, sellFirmId, tradeSource }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length, TradeIndicator.encode_length, TradeSource.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TradeSource.decode_encode, some_bind]
  rfl

end TradeMessage

/-- News Message: 891 bytes -/
structure NewsMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  newsId : BitVec 32
  firmCode : Alpha 30
  title : Alpha 81
  referenceNullTerminatedChar256 : Alpha 256
  newsText : Alpha 512
  deriving DecidableEq, Repr

namespace NewsMessage

def encode (message : NewsMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.newsId
    ++ (Alpha.encode message.firmCode
    ++ (Alpha.encode message.title
    ++ (Alpha.encode message.referenceNullTerminatedChar256
    ++ (Alpha.encode message.newsText))))))

def decode (bytes : List UInt8) : Option (NewsMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (newsId, bytes) ← decodeUInt 4 bytes
  let (firmCode, bytes) ← Alpha.decode 30 bytes
  let (title, bytes) ← Alpha.decode 81 bytes
  let (referenceNullTerminatedChar256, bytes) ← Alpha.decode 256 bytes
  let (newsText, bytes) ← Alpha.decode 512 bytes
  pure ({ timestamp, orderbook, newsId, firmCode, title, referenceNullTerminatedChar256, newsText }, bytes)

@[simp] theorem encode_length (message : NewsMessage) : (encode message).length = 891 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : NewsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewsMessage

/-- Index Member Directory Message: 20 bytes -/
structure IndexMemberDirectoryMessage where
  timestamp : BitVec 32
  indexOrderbook : BitVec 32
  memberOrderbook : BitVec 32
  weight : BitVec 64
  deriving DecidableEq, Repr

namespace IndexMemberDirectoryMessage

def encode (message : IndexMemberDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.indexOrderbook
    ++ (encodeUInt 4 message.memberOrderbook
    ++ (encodeUInt 8 message.weight)))

def decode (bytes : List UInt8) : Option (IndexMemberDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (indexOrderbook, bytes) ← decodeUInt 4 bytes
  let (memberOrderbook, bytes) ← decodeUInt 4 bytes
  let (weight, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, indexOrderbook, memberOrderbook, weight }, bytes)

@[simp] theorem encode_length (message : IndexMemberDirectoryMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : IndexMemberDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexMemberDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndexMemberDirectoryMessage

/-- Index Value Message: 16 bytes -/
structure IndexValueMessage where
  timestamp : BitVec 32
  indexOrderbook : BitVec 32
  indexValue : BitVec 64
  deriving DecidableEq, Repr

namespace IndexValueMessage

def encode (message : IndexValueMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.indexOrderbook
    ++ (encodeUInt 8 message.indexValue))

def decode (bytes : List UInt8) : Option (IndexValueMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (indexOrderbook, bytes) ← decodeUInt 4 bytes
  let (indexValue, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, indexOrderbook, indexValue }, bytes)

@[simp] theorem encode_length (message : IndexValueMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : IndexValueMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexValueMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndexValueMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | timestampMessage (message : TimestampMessage) -- "T" 0x54
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | priceTickSizeMessage (message : PriceTickSizeMessage) -- "L" 0x4C
  | quantityTickSizeMessage (message : QuantityTickSizeMessage) -- "M" 0x4D
  | orderbookDirectoryMessage (message : OrderbookDirectoryMessage) -- "R" 0x52
  | orderbookTradingActionMessage (message : OrderbookTradingActionMessage) -- "H" 0x48
  | orderbookAttributeMessage (message : OrderbookAttributeMessage) -- "X" 0x58
  | firmDirectoryMessage (message : FirmDirectoryMessage) -- "F" 0x46
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- "C" 0x43
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  | orderDeleteMessage (message : OrderDeleteMessage) -- "D" 0x44
  | orderReplaceMessage (message : OrderReplaceMessage) -- "U" 0x55
  | indicativePriceQuantityMessage (message : IndicativePriceQuantityMessage) -- "I" 0x49
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | newsMessage (message : NewsMessage) -- "N" 0x4E
  | indexMemberDirectoryMessage (message : IndexMemberDirectoryMessage) -- "Y" 0x59
  | indexValueMessage (message : IndexValueMessage) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .timestampMessage _ => 84
  | .systemEventMessage _ => 83
  | .priceTickSizeMessage _ => 76
  | .quantityTickSizeMessage _ => 77
  | .orderbookDirectoryMessage _ => 82
  | .orderbookTradingActionMessage _ => 72
  | .orderbookAttributeMessage _ => 88
  | .firmDirectoryMessage _ => 70
  | .addOrderMessage _ => 65
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .brokenTradeMessage _ => 66
  | .orderDeleteMessage _ => 68
  | .orderReplaceMessage _ => 85
  | .indicativePriceQuantityMessage _ => 73
  | .tradeMessage _ => 80
  | .newsMessage _ => 78
  | .indexMemberDirectoryMessage _ => 89
  | .indexValueMessage _ => 90

def encode : SequencedMessage → List UInt8
  | .timestampMessage message => TimestampMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .priceTickSizeMessage message => PriceTickSizeMessage.encode message
  | .quantityTickSizeMessage message => QuantityTickSizeMessage.encode message
  | .orderbookDirectoryMessage message => OrderbookDirectoryMessage.encode message
  | .orderbookTradingActionMessage message => OrderbookTradingActionMessage.encode message
  | .orderbookAttributeMessage message => OrderbookAttributeMessage.encode message
  | .firmDirectoryMessage message => FirmDirectoryMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderReplaceMessage message => OrderReplaceMessage.encode message
  | .indicativePriceQuantityMessage message => IndicativePriceQuantityMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .newsMessage message => NewsMessage.encode message
  | .indexMemberDirectoryMessage message => IndexMemberDirectoryMessage.encode message
  | .indexValueMessage message => IndexValueMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 891 := by
  cases message with
  | timestampMessage inner =>
    simp only [encode, TimestampMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | priceTickSizeMessage inner =>
    simp only [encode, PriceTickSizeMessage.encode_length]
    omega
  | quantityTickSizeMessage inner =>
    simp only [encode, QuantityTickSizeMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [encode, OrderbookDirectoryMessage.encode_length]
    omega
  | orderbookTradingActionMessage inner =>
    simp only [encode, OrderbookTradingActionMessage.encode_length]
    omega
  | orderbookAttributeMessage inner =>
    simp only [encode, OrderbookAttributeMessage.encode_length]
    omega
  | firmDirectoryMessage inner =>
    simp only [encode, FirmDirectoryMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [encode, OrderExecutedWithPriceMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [encode, OrderDeleteMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [encode, OrderReplaceMessage.encode_length]
    omega
  | indicativePriceQuantityMessage inner =>
    simp only [encode, IndicativePriceQuantityMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | newsMessage inner =>
    simp only [encode, NewsMessage.encode_length]
    omega
  | indexMemberDirectoryMessage inner =>
    simp only [encode, IndexMemberDirectoryMessage.encode_length]
    omega
  | indexValueMessage inner =>
    simp only [encode, IndexValueMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 84 then (TimestampMessage.decode bytes).map fun (message, rest) => (.timestampMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 76 then (PriceTickSizeMessage.decode bytes).map fun (message, rest) => (.priceTickSizeMessage message, rest)
  else if tag = 77 then (QuantityTickSizeMessage.decode bytes).map fun (message, rest) => (.quantityTickSizeMessage message, rest)
  else if tag = 82 then (OrderbookDirectoryMessage.decode bytes).map fun (message, rest) => (.orderbookDirectoryMessage message, rest)
  else if tag = 72 then (OrderbookTradingActionMessage.decode bytes).map fun (message, rest) => (.orderbookTradingActionMessage message, rest)
  else if tag = 88 then (OrderbookAttributeMessage.decode bytes).map fun (message, rest) => (.orderbookAttributeMessage message, rest)
  else if tag = 70 then (FirmDirectoryMessage.decode bytes).map fun (message, rest) => (.firmDirectoryMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 85 then (OrderReplaceMessage.decode bytes).map fun (message, rest) => (.orderReplaceMessage message, rest)
  else if tag = 73 then (IndicativePriceQuantityMessage.decode bytes).map fun (message, rest) => (.indicativePriceQuantityMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 78 then (NewsMessage.decode bytes).map fun (message, rest) => (.newsMessage message, rest)
  else if tag = 89 then (IndexMemberDirectoryMessage.decode bytes).map fun (message, rest) => (.indexMemberDirectoryMessage message, rest)
  else if tag = 90 then (IndexValueMessage.decode bytes).map fun (message, rest) => (.indexValueMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 892 := by
  unfold encode
  cases message.sequencedMessage with
  | timestampMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TimestampMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | priceTickSizeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, PriceTickSizeMessage.encode_length]
    omega
  | quantityTickSizeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, QuantityTickSizeMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderbookDirectoryMessage.encode_length]
    omega
  | orderbookTradingActionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderbookTradingActionMessage.encode_length]
    omega
  | orderbookAttributeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderbookAttributeMessage.encode_length]
    omega
  | firmDirectoryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, FirmDirectoryMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderReplaceMessage.encode_length]
    omega
  | indicativePriceQuantityMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, IndicativePriceQuantityMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | newsMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, NewsMessage.encode_length]
    omega
  | indexMemberDirectoryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, IndexMemberDirectoryMessage.encode_length]
    omega
  | indexValueMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, IndexValueMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedDataPacket

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServerHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServerHeartbeat

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfSession) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EndOfSession

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | serverHeartbeat (message : ServerHeartbeat) -- "H" 0x48
  | endOfSession (message : EndOfSession) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83
  | .serverHeartbeat _ => 72
  | .endOfSession _ => 90

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .endOfSession message => EndOfSession.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 64642 := by
  cases message with
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
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ServerPayload :=
  if tag = 43 then (DebugPacket.decode bytes).map fun message => .debugPacket message
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginAcceptedPacket message) else none
  else if tag = 74 then (LoginRejectedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRejectedPacket message) else none
  else if tag = 83 then (SequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedDataPacket message) else none
  else if tag = 72 then (ServerHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeat message) else none
  else if tag = 90 then (EndOfSession.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfSession message) else none
  else none

theorem decode_encode (message : ServerPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode]
  | loginAcceptedPacket message => simp [decode, encode, tag, LoginAcceptedPacket.decode_encode_nil]
  | loginRejectedPacket message => simp [decode, encode, tag, LoginRejectedPacket.decode_encode_nil]
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode_nil]
  | serverHeartbeat message => simp [decode, encode, tag, ServerHeartbeat.decode_encode_nil]
  | endOfSession message => simp [decode, encode, tag, EndOfSession.decode_encode_nil]

end ServerPayload

/-- Server Soup Bin Tcp Packet -/
structure ServerSoupBinTcpPacket where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupBinTcpPacket

def encodeBody (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option ServerSoupBinTcpPacket := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let serverPayload ← ServerPayload.decode serverPacketType bytes
  pure { serverPayload }

theorem decodeBody_encodeBody (message : ServerSoupBinTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverPayload with
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
    omega
  | serverHeartbeat inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, EndOfSession.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ServerSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ServerSoupBinTcpPacket × List UInt8) :=
  decodeFramedAll 2 0 decodeBody

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAll_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ServerSoupBinTcpPacket

/-- Server Packet -/
structure ServerPacket where
  serverSoupBinTcpPacket : List ServerSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSoupBinTcpPacket.encode message.serverSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSoupBinTcpPacket ← decodeAll ServerSoupBinTcpPacket.decode bytes.length bytes
  pure { serverSoupBinTcpPacket }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.decode ServerSoupBinTcpPacket.decode_encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket _ (encodeMany_length_ge ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket), some_bind]
  rfl

end ServerPacket

end Omi.NsxaustraliaNetsMarketdatafeedItchV4255Server
