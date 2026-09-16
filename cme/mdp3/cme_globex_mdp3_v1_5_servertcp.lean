import Omi.Wire

/-!
# CME Group Market Data Platform 3 v1.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Match Event Indicator is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Settl Price Type is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Inst Attrib Value is a bit field set, proven as its 4 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CmeGlobexMdp3SbeV15ServerTcp

/-- Security Update Action: one byte code -/
inductive SecurityUpdateAction where
  | add -- Add
  | delete -- Delete
  | modify -- Modify
  deriving DecidableEq, Repr

namespace SecurityUpdateAction

def toByte : SecurityUpdateAction → UInt8
  | .add => 0x41
  | .delete => 0x44
  | .modify => 0x4D

def ofByte? (byte : UInt8) : Option SecurityUpdateAction :=
  if byte = 0x41 then some .add
  else if byte = 0x44 then some .delete
  else if byte = 0x4D then some .modify
  else none

theorem ofByte?_toByte (value : SecurityUpdateAction) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : SecurityUpdateAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityUpdateAction × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityUpdateAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityUpdateAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end SecurityUpdateAction

/-- Md Entry Type Book: one byte code -/
inductive MdEntryTypeBook where
  | bid -- Bid
  | offer -- Offer
  | impliedBid -- Implied Bid
  | impliedOffer -- Implied Offer
  | bookReset -- Book Reset
  deriving DecidableEq, Repr

namespace MdEntryTypeBook

def toByte : MdEntryTypeBook → UInt8
  | .bid => 0x30
  | .offer => 0x31
  | .impliedBid => 0x45
  | .impliedOffer => 0x46
  | .bookReset => 0x4A

def ofByte? (byte : UInt8) : Option MdEntryTypeBook :=
  if byte = 0x30 then some .bid
  else if byte = 0x31 then some .offer
  else if byte = 0x45 then some .impliedBid
  else if byte = 0x46 then some .impliedOffer
  else if byte = 0x4A then some .bookReset
  else none

theorem ofByte?_toByte (value : MdEntryTypeBook) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : MdEntryTypeBook) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeBook × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeBook) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeBook) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end MdEntryTypeBook

/-- Md Entry Type Daily Statistics: one byte code -/
inductive MdEntryTypeDailyStatistics where
  | settlementPrice -- Settlement Price
  | clearedVolume -- Cleared Volume
  | openInterest -- Open Interest
  | fixingPrice -- Fixing Price
  deriving DecidableEq, Repr

namespace MdEntryTypeDailyStatistics

def toByte : MdEntryTypeDailyStatistics → UInt8
  | .settlementPrice => 0x36
  | .clearedVolume => 0x42
  | .openInterest => 0x43
  | .fixingPrice => 0x57

def ofByte? (byte : UInt8) : Option MdEntryTypeDailyStatistics :=
  if byte = 0x36 then some .settlementPrice
  else if byte = 0x42 then some .clearedVolume
  else if byte = 0x43 then some .openInterest
  else if byte = 0x57 then some .fixingPrice
  else none

theorem ofByte?_toByte (value : MdEntryTypeDailyStatistics) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : MdEntryTypeDailyStatistics) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeDailyStatistics × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeDailyStatistics) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeDailyStatistics) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end MdEntryTypeDailyStatistics

/-- Md Entry Type Statistics: one byte code -/
inductive MdEntryTypeStatistics where
  | openPrice -- Open Price
  | highTrade -- High Trade
  | lowTrade -- Low Trade
  | highestBid -- Highest Bid
  | lowestOffer -- Lowest Offer
  deriving DecidableEq, Repr

namespace MdEntryTypeStatistics

def toByte : MdEntryTypeStatistics → UInt8
  | .openPrice => 0x34
  | .highTrade => 0x37
  | .lowTrade => 0x38
  | .highestBid => 0x4E
  | .lowestOffer => 0x4F

def ofByte? (byte : UInt8) : Option MdEntryTypeStatistics :=
  if byte = 0x34 then some .openPrice
  else if byte = 0x37 then some .highTrade
  else if byte = 0x38 then some .lowTrade
  else if byte = 0x4E then some .highestBid
  else if byte = 0x4F then some .lowestOffer
  else none

theorem ofByte?_toByte (value : MdEntryTypeStatistics) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : MdEntryTypeStatistics) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeStatistics × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeStatistics) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeStatistics) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end MdEntryTypeStatistics

/-- Md Entry Type: one byte code -/
inductive MdEntryType where
  | bid -- Bid
  | offer -- Offer
  | trade -- Trade
  | openingPrice -- Opening Price
  | settlementPrice -- Settlement Price
  | tradingSessionHighPrice -- Trading Session High Price
  | tradingSessionLowPrice -- Trading Session Low Price
  | tradeVolume -- Trade Volume
  | openInterest -- Open Interest
  | impliedBid -- Implied Bid
  | impliedOffer -- Implied Offer
  | emptyBook -- Empty Book
  | sessionHighBid -- Session High Bid
  | sessionLowOffer -- Session Low Offer
  | fixingPrice -- Fixing Price
  | electronicVolume -- Electronic Volume
  | thresholdLimitsandPriceBandVariation -- Threshold Limitsand Price Band Variation
  deriving DecidableEq, Repr

namespace MdEntryType

def toByte : MdEntryType → UInt8
  | .bid => 0x30
  | .offer => 0x31
  | .trade => 0x32
  | .openingPrice => 0x34
  | .settlementPrice => 0x36
  | .tradingSessionHighPrice => 0x37
  | .tradingSessionLowPrice => 0x38
  | .tradeVolume => 0x42
  | .openInterest => 0x43
  | .impliedBid => 0x45
  | .impliedOffer => 0x46
  | .emptyBook => 0x4A
  | .sessionHighBid => 0x4E
  | .sessionLowOffer => 0x4F
  | .fixingPrice => 0x57
  | .electronicVolume => 0x65
  | .thresholdLimitsandPriceBandVariation => 0x67

def ofByte? (byte : UInt8) : Option MdEntryType :=
  if byte = 0x30 then some .bid
  else if byte = 0x31 then some .offer
  else if byte = 0x32 then some .trade
  else if byte = 0x34 then some .openingPrice
  else if byte = 0x36 then some .settlementPrice
  else if byte = 0x37 then some .tradingSessionHighPrice
  else if byte = 0x38 then some .tradingSessionLowPrice
  else if byte = 0x42 then some .tradeVolume
  else if byte = 0x43 then some .openInterest
  else if byte = 0x45 then some .impliedBid
  else if byte = 0x46 then some .impliedOffer
  else if byte = 0x4A then some .emptyBook
  else if byte = 0x4E then some .sessionHighBid
  else if byte = 0x4F then some .sessionLowOffer
  else if byte = 0x57 then some .fixingPrice
  else if byte = 0x65 then some .electronicVolume
  else if byte = 0x67 then some .thresholdLimitsandPriceBandVariation
  else none

theorem ofByte?_toByte (value : MdEntryType) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : MdEntryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryType × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end MdEntryType

/-- Server Technical Header: 14 bytes -/
structure ServerTechnicalHeader where
  encodingType : BitVec 16
  messageSequenceNumber : BitVec 32
  tcpSendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace ServerTechnicalHeader

def encode (message : ServerTechnicalHeader) : List UInt8 :=
  encodeUIntLE 2 message.encodingType
    ++ encodeUIntLE 4 message.messageSequenceNumber
    ++ encodeUIntLE 8 message.tcpSendingTime

def decode (bytes : List UInt8) : Option (ServerTechnicalHeader × List UInt8) := do
  let (encodingType, bytes) ← decodeUIntLE 2 bytes
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (tcpSendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ encodingType, messageSequenceNumber, tcpSendingTime }, bytes)

@[simp] theorem encode_length (message : ServerTechnicalHeader) : (encode message).length = 14 := by
  simp [encode]

theorem encode_length_pos (message : ServerTechnicalHeader) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerTechnicalHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end ServerTechnicalHeader

/-- Channel Reset Group: 2 bytes -/
structure ChannelResetGroup where
  applId : BitVec 16
  deriving DecidableEq, Repr

namespace ChannelResetGroup

def encode (message : ChannelResetGroup) : List UInt8 :=
  encodeUIntLE 2 message.applId

def decode (bytes : List UInt8) : Option (ChannelResetGroup × List UInt8) := do
  let (applId, bytes) ← decodeUIntLE 2 bytes
  pure ({ applId }, bytes)

@[simp] theorem encode_length (message : ChannelResetGroup) : (encode message).length = 2 := by
  simp [encode]

theorem encode_length_pos (message : ChannelResetGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ChannelResetGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end ChannelResetGroup

/-- Channel Reset -/
structure ChannelReset where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  blockLength : BitVec 16
  channelResetGroup : Bounded 1 ChannelResetGroup
  deriving DecidableEq, Repr

namespace ChannelReset

def encode (message : ChannelReset) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.channelResetGroup.val.length)
    ++ encodeMany ChannelResetGroup.encode message.channelResetGroup.val

def decode (bytes : List UInt8) : Option (ChannelReset × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (channelResetGroup_, bytes) ← decodeMany ChannelResetGroup.decode numInGroup.toNat bytes
  if fits_channelResetGroup : channelResetGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, blockLength, channelResetGroup := ⟨channelResetGroup_, fits_channelResetGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : ChannelReset) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_channelResetGroup : message.channelResetGroup.val.length < 256 := by simpa using message.channelResetGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_channelResetGroup, fits_channelResetGroup, decodeMany_encodeMany ChannelResetGroup.encode ChannelResetGroup.decode ChannelResetGroup.decode_encode]

end ChannelReset

/-- Admin Heartbeat: 0 bytes -/
structure AdminHeartbeat where
  deriving DecidableEq, Repr

namespace AdminHeartbeat

def encode (_ : AdminHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (AdminHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : AdminHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : AdminHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end AdminHeartbeat

/-- Admin Login: 1 bytes -/
structure AdminLogin where
  heartBtInt : BitVec 8
  deriving DecidableEq, Repr

namespace AdminLogin

def encode (message : AdminLogin) : List UInt8 :=
  encodeUInt 1 message.heartBtInt

def decode (bytes : List UInt8) : Option (AdminLogin × List UInt8) := do
  let (heartBtInt, bytes) ← decodeUInt 1 bytes
  pure ({ heartBtInt }, bytes)

@[simp] theorem encode_length (message : AdminLogin) : (encode message).length = 1 := by
  simp [encode]

theorem encode_length_pos (message : AdminLogin) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : AdminLogin) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end AdminLogin

/-- Admin Logout: 100 bytes -/
structure AdminLogout where
  text : Alpha 100
  deriving DecidableEq, Repr

namespace AdminLogout

def encode (message : AdminLogout) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (AdminLogout × List UInt8) := do
  let (text, bytes) ← Alpha.decode 100 bytes
  pure ({ text }, bytes)

@[simp] theorem encode_length (message : AdminLogout) : (encode message).length = 100 := by
  simp [encode]

theorem encode_length_pos (message : AdminLogout) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : AdminLogout) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end AdminLogout

/-- Maturity Month Year: 5 bytes -/
structure MaturityMonthYear where
  year : BitVec 16
  month : BitVec 8
  day : BitVec 8
  week : BitVec 8
  deriving DecidableEq, Repr

namespace MaturityMonthYear

def encode (message : MaturityMonthYear) : List UInt8 :=
  encodeUIntLE 2 message.year
    ++ encodeUInt 1 message.month
    ++ encodeUInt 1 message.day
    ++ encodeUInt 1 message.week

def decode (bytes : List UInt8) : Option (MaturityMonthYear × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 2 bytes
  let (month, bytes) ← decodeUInt 1 bytes
  let (day, bytes) ← decodeUInt 1 bytes
  let (week, bytes) ← decodeUInt 1 bytes
  pure ({ year, month, day, week }, bytes)

@[simp] theorem encode_length (message : MaturityMonthYear) : (encode message).length = 5 := by
  simp [encode]

theorem encode_length_pos (message : MaturityMonthYear) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : MaturityMonthYear) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end MaturityMonthYear

/-- Events Group: 9 bytes -/
structure EventsGroup where
  eventType : BitVec 8
  eventTime : BitVec 64
  deriving DecidableEq, Repr

namespace EventsGroup

def encode (message : EventsGroup) : List UInt8 :=
  encodeUInt 1 message.eventType
    ++ encodeUIntLE 8 message.eventTime

def decode (bytes : List UInt8) : Option (EventsGroup × List UInt8) := do
  let (eventType, bytes) ← decodeUInt 1 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ eventType, eventTime }, bytes)

@[simp] theorem encode_length (message : EventsGroup) : (encode message).length = 9 := by
  simp [encode]

theorem encode_length_pos (message : EventsGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EventsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end EventsGroup

/-- Feed Types Group: 4 bytes -/
structure FeedTypesGroup where
  mdFeedType : Alpha 3
  marketDepth : BitVec 8
  deriving DecidableEq, Repr

namespace FeedTypesGroup

def encode (message : FeedTypesGroup) : List UInt8 :=
  Alpha.encode message.mdFeedType
    ++ encodeUInt 1 message.marketDepth

def decode (bytes : List UInt8) : Option (FeedTypesGroup × List UInt8) := do
  let (mdFeedType, bytes) ← Alpha.decode 3 bytes
  let (marketDepth, bytes) ← decodeUInt 1 bytes
  pure ({ mdFeedType, marketDepth }, bytes)

@[simp] theorem encode_length (message : FeedTypesGroup) : (encode message).length = 4 := by
  simp [encode]

theorem encode_length_pos (message : FeedTypesGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : FeedTypesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end FeedTypesGroup

/-- Inst Attrib Group: 4 bytes -/
structure InstAttribGroup where
  instAttribValue : BitVec 32
  deriving DecidableEq, Repr

namespace InstAttribGroup

def encode (message : InstAttribGroup) : List UInt8 :=
  encodeUIntLE 4 message.instAttribValue

def decode (bytes : List UInt8) : Option (InstAttribGroup × List UInt8) := do
  let (instAttribValue, bytes) ← decodeUIntLE 4 bytes
  pure ({ instAttribValue }, bytes)

@[simp] theorem encode_length (message : InstAttribGroup) : (encode message).length = 4 := by
  simp [encode]

theorem encode_length_pos (message : InstAttribGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : InstAttribGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end InstAttribGroup

/-- Lot Type Rules Group: 5 bytes -/
structure LotTypeRulesGroup where
  lotType : BitVec 8
  minLotSize : BitVec 32
  deriving DecidableEq, Repr

namespace LotTypeRulesGroup

def encode (message : LotTypeRulesGroup) : List UInt8 :=
  encodeUInt 1 message.lotType
    ++ encodeUIntLE 4 message.minLotSize

def decode (bytes : List UInt8) : Option (LotTypeRulesGroup × List UInt8) := do
  let (lotType, bytes) ← decodeUInt 1 bytes
  let (minLotSize, bytes) ← decodeUIntLE 4 bytes
  pure ({ lotType, minLotSize }, bytes)

@[simp] theorem encode_length (message : LotTypeRulesGroup) : (encode message).length = 5 := by
  simp [encode]

theorem encode_length_pos (message : LotTypeRulesGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LotTypeRulesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end LotTypeRulesGroup

/-- Md Instrument Definition Future -/
structure MdInstrumentDefinitionFuture where
  matchEventIndicator : BitVec 8
  totNumReportsOptional : BitVec 32
  securityUpdateAction : SecurityUpdateAction
  lastUpdateTime : BitVec 64
  mdSecurityTradingStatus : BitVec 8
  applId : BitVec 16
  marketSegmentId : BitVec 8
  underlyingProduct : BitVec 8
  securityExchange : Alpha 4
  securityGroup : Alpha 6
  asset : Alpha 6
  symbol : Alpha 20
  securityId : BitVec 32
  securityType : Alpha 6
  cfiCode : Alpha 6
  maturityMonthYear : MaturityMonthYear
  currency : Alpha 3
  settlCurrency : Alpha 3
  matchAlgorithm : Alpha 1
  minTradeVol : BitVec 32
  maxTradeVol : BitVec 32
  minPriceIncrement : BitVec 64
  displayFactor : BitVec 64
  mainFraction : BitVec 8
  subFraction : BitVec 8
  priceDisplayFormat : BitVec 8
  unitOfMeasure : Alpha 30
  unitOfMeasureQty : BitVec 64
  tradingReferencePrice : BitVec 64
  settlPriceType : BitVec 8
  openInterestQty : BitVec 32
  clearedVolume : BitVec 32
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  decayQuantity : BitVec 32
  decayStartDate : BitVec 16
  originalContractSize : BitVec 32
  contractMultiplier : BitVec 32
  contractMultiplierUnit : BitVec 8
  flowScheduleType : BitVec 8
  minPriceIncrementAmount : BitVec 64
  userDefinedInstrument : Alpha 1
  blockLength : BitVec 16
  eventsGroup : Bounded 1 EventsGroup
  blockLength : BitVec 16
  feedTypesGroup : Bounded 1 FeedTypesGroup
  blockLength : BitVec 16
  instAttribGroup : Bounded 1 InstAttribGroup
  blockLength : BitVec 16
  lotTypeRulesGroup : Bounded 1 LotTypeRulesGroup
  deriving DecidableEq, Repr

namespace MdInstrumentDefinitionFuture

def encode (message : MdInstrumentDefinitionFuture) : List UInt8 :=
  encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 4 message.totNumReportsOptional
    ++ SecurityUpdateAction.encode message.securityUpdateAction
    ++ encodeUIntLE 8 message.lastUpdateTime
    ++ encodeUInt 1 message.mdSecurityTradingStatus
    ++ encodeUIntLE 2 message.applId
    ++ encodeUInt 1 message.marketSegmentId
    ++ encodeUInt 1 message.underlyingProduct
    ++ Alpha.encode message.securityExchange
    ++ Alpha.encode message.securityGroup
    ++ Alpha.encode message.asset
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 4 message.securityId
    ++ Alpha.encode message.securityType
    ++ Alpha.encode message.cfiCode
    ++ MaturityMonthYear.encode message.maturityMonthYear
    ++ Alpha.encode message.currency
    ++ Alpha.encode message.settlCurrency
    ++ Alpha.encode message.matchAlgorithm
    ++ encodeUIntLE 4 message.minTradeVol
    ++ encodeUIntLE 4 message.maxTradeVol
    ++ encodeUIntLE 8 message.minPriceIncrement
    ++ encodeUIntLE 8 message.displayFactor
    ++ encodeUInt 1 message.mainFraction
    ++ encodeUInt 1 message.subFraction
    ++ encodeUInt 1 message.priceDisplayFormat
    ++ Alpha.encode message.unitOfMeasure
    ++ encodeUIntLE 8 message.unitOfMeasureQty
    ++ encodeUIntLE 8 message.tradingReferencePrice
    ++ encodeUIntLE 1 message.settlPriceType
    ++ encodeUIntLE 4 message.openInterestQty
    ++ encodeUIntLE 4 message.clearedVolume
    ++ encodeUIntLE 8 message.highLimitPrice
    ++ encodeUIntLE 8 message.lowLimitPrice
    ++ encodeUIntLE 8 message.maxPriceVariation
    ++ encodeUIntLE 4 message.decayQuantity
    ++ encodeUIntLE 2 message.decayStartDate
    ++ encodeUIntLE 4 message.originalContractSize
    ++ encodeUIntLE 4 message.contractMultiplier
    ++ encodeUInt 1 message.contractMultiplierUnit
    ++ encodeUInt 1 message.flowScheduleType
    ++ encodeUIntLE 8 message.minPriceIncrementAmount
    ++ Alpha.encode message.userDefinedInstrument
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.eventsGroup.val.length)
    ++ encodeMany EventsGroup.encode message.eventsGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.feedTypesGroup.val.length)
    ++ encodeMany FeedTypesGroup.encode message.feedTypesGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.instAttribGroup.val.length)
    ++ encodeMany InstAttribGroup.encode message.instAttribGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.lotTypeRulesGroup.val.length)
    ++ encodeMany LotTypeRulesGroup.encode message.lotTypeRulesGroup.val

def decode (bytes : List UInt8) : Option (MdInstrumentDefinitionFuture × List UInt8) := do
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (totNumReportsOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityUpdateAction, bytes) ← SecurityUpdateAction.decode bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (mdSecurityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (applId, bytes) ← decodeUIntLE 2 bytes
  let (marketSegmentId, bytes) ← decodeUInt 1 bytes
  let (underlyingProduct, bytes) ← decodeUInt 1 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  let (asset, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (securityType, bytes) ← Alpha.decode 6 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (settlCurrency, bytes) ← Alpha.decode 3 bytes
  let (matchAlgorithm, bytes) ← Alpha.decode 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (maxTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (minPriceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (displayFactor, bytes) ← decodeUIntLE 8 bytes
  let (mainFraction, bytes) ← decodeUInt 1 bytes
  let (subFraction, bytes) ← decodeUInt 1 bytes
  let (priceDisplayFormat, bytes) ← decodeUInt 1 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 30 bytes
  let (unitOfMeasureQty, bytes) ← decodeUIntLE 8 bytes
  let (tradingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (openInterestQty, bytes) ← decodeUIntLE 4 bytes
  let (clearedVolume, bytes) ← decodeUIntLE 4 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (decayQuantity, bytes) ← decodeUIntLE 4 bytes
  let (decayStartDate, bytes) ← decodeUIntLE 2 bytes
  let (originalContractSize, bytes) ← decodeUIntLE 4 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 4 bytes
  let (contractMultiplierUnit, bytes) ← decodeUInt 1 bytes
  let (flowScheduleType, bytes) ← decodeUInt 1 bytes
  let (minPriceIncrementAmount, bytes) ← decodeUIntLE 8 bytes
  let (userDefinedInstrument, bytes) ← Alpha.decode 1 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (eventsGroup_, bytes) ← decodeMany EventsGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (feedTypesGroup_, bytes) ← decodeMany FeedTypesGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (instAttribGroup_, bytes) ← decodeMany InstAttribGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (lotTypeRulesGroup_, bytes) ← decodeMany LotTypeRulesGroup.decode numInGroup.toNat bytes
  if fits_eventsGroup : eventsGroup_.length < 256 then
    if fits_feedTypesGroup : feedTypesGroup_.length < 256 then
      if fits_instAttribGroup : instAttribGroup_.length < 256 then
        if fits_lotTypeRulesGroup : lotTypeRulesGroup_.length < 256 then
          pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, maturityMonthYear, currency, settlCurrency, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrement, displayFactor, mainFraction, subFraction, priceDisplayFormat, unitOfMeasure, unitOfMeasureQty, tradingReferencePrice, settlPriceType, openInterestQty, clearedVolume, highLimitPrice, lowLimitPrice, maxPriceVariation, decayQuantity, decayStartDate, originalContractSize, contractMultiplier, contractMultiplierUnit, flowScheduleType, minPriceIncrementAmount, userDefinedInstrument, blockLength, eventsGroup := ⟨eventsGroup_, fits_eventsGroup⟩, blockLength, feedTypesGroup := ⟨feedTypesGroup_, fits_feedTypesGroup⟩, blockLength, instAttribGroup := ⟨instAttribGroup_, fits_instAttribGroup⟩, blockLength, lotTypeRulesGroup := ⟨lotTypeRulesGroup_, fits_lotTypeRulesGroup⟩ }, bytes)
        else none
      else none
    else none
  else none

@[simp] theorem decode_encode (message : MdInstrumentDefinitionFuture) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_eventsGroup : message.eventsGroup.val.length < 256 := by simpa using message.eventsGroup.length_lt
  have fits_feedTypesGroup : message.feedTypesGroup.val.length < 256 := by simpa using message.feedTypesGroup.length_lt
  have fits_instAttribGroup : message.instAttribGroup.val.length < 256 := by simpa using message.instAttribGroup.length_lt
  have fits_lotTypeRulesGroup : message.lotTypeRulesGroup.val.length < 256 := by simpa using message.lotTypeRulesGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_eventsGroup, fits_eventsGroup, decodeMany_encodeMany EventsGroup.encode EventsGroup.decode EventsGroup.decode_encode, Nat.mod_eq_of_lt fits_feedTypesGroup, fits_feedTypesGroup, decodeMany_encodeMany FeedTypesGroup.encode FeedTypesGroup.decode FeedTypesGroup.decode_encode, Nat.mod_eq_of_lt fits_instAttribGroup, fits_instAttribGroup, decodeMany_encodeMany InstAttribGroup.encode InstAttribGroup.decode InstAttribGroup.decode_encode, Nat.mod_eq_of_lt fits_lotTypeRulesGroup, fits_lotTypeRulesGroup, decodeMany_encodeMany LotTypeRulesGroup.encode LotTypeRulesGroup.decode LotTypeRulesGroup.decode_encode]

end MdInstrumentDefinitionFuture

/-- Legacy Legs Group: 18 bytes -/
structure LegacyLegsGroup where
  legSecurityId : BitVec 32
  legSide : BitVec 8
  legRatioQty : BitVec 8
  legPrice : BitVec 64
  legOptionDelta : BitVec 32
  deriving DecidableEq, Repr

namespace LegacyLegsGroup

def encode (message : LegacyLegsGroup) : List UInt8 :=
  encodeUIntLE 4 message.legSecurityId
    ++ encodeUInt 1 message.legSide
    ++ encodeUInt 1 message.legRatioQty
    ++ encodeUIntLE 8 message.legPrice
    ++ encodeUIntLE 4 message.legOptionDelta

def decode (bytes : List UInt8) : Option (LegacyLegsGroup × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (legRatioQty, bytes) ← decodeUInt 1 bytes
  let (legPrice, bytes) ← decodeUIntLE 8 bytes
  let (legOptionDelta, bytes) ← decodeUIntLE 4 bytes
  pure ({ legSecurityId, legSide, legRatioQty, legPrice, legOptionDelta }, bytes)

@[simp] theorem encode_length (message : LegacyLegsGroup) : (encode message).length = 18 := by
  simp [encode]

theorem encode_length_pos (message : LegacyLegsGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LegacyLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end LegacyLegsGroup

/-- Md Instrument Definition Spread -/
structure MdInstrumentDefinitionSpread where
  matchEventIndicator : BitVec 8
  totNumReportsOptional : BitVec 32
  securityUpdateAction : SecurityUpdateAction
  lastUpdateTime : BitVec 64
  mdSecurityTradingStatus : BitVec 8
  applId : BitVec 16
  marketSegmentId : BitVec 8
  underlyingProductOptional : BitVec 8
  securityExchange : Alpha 4
  securityGroup : Alpha 6
  asset : Alpha 6
  symbol : Alpha 20
  securityId : BitVec 32
  securityType : Alpha 6
  cfiCode : Alpha 6
  maturityMonthYear : MaturityMonthYear
  currency : Alpha 3
  securitySubType : Alpha 5
  userDefinedInstrument : Alpha 1
  matchAlgorithm : Alpha 1
  minTradeVol : BitVec 32
  maxTradeVol : BitVec 32
  minPriceIncrement : BitVec 64
  displayFactor : BitVec 64
  priceDisplayFormat : BitVec 8
  priceRatio : BitVec 64
  tickRule : BitVec 8
  unitOfMeasure : Alpha 30
  tradingReferencePrice : BitVec 64
  settlPriceType : BitVec 8
  openInterestQty : BitVec 32
  clearedVolume : BitVec 32
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  mainFraction : BitVec 8
  subFraction : BitVec 8
  blockLength : BitVec 16
  eventsGroup : Bounded 1 EventsGroup
  blockLength : BitVec 16
  feedTypesGroup : Bounded 1 FeedTypesGroup
  blockLength : BitVec 16
  instAttribGroup : Bounded 1 InstAttribGroup
  blockLength : BitVec 16
  lotTypeRulesGroup : Bounded 1 LotTypeRulesGroup
  blockLength : BitVec 16
  legacyLegsGroup : Bounded 1 LegacyLegsGroup
  deriving DecidableEq, Repr

namespace MdInstrumentDefinitionSpread

def encode (message : MdInstrumentDefinitionSpread) : List UInt8 :=
  encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 4 message.totNumReportsOptional
    ++ SecurityUpdateAction.encode message.securityUpdateAction
    ++ encodeUIntLE 8 message.lastUpdateTime
    ++ encodeUInt 1 message.mdSecurityTradingStatus
    ++ encodeUIntLE 2 message.applId
    ++ encodeUInt 1 message.marketSegmentId
    ++ encodeUInt 1 message.underlyingProductOptional
    ++ Alpha.encode message.securityExchange
    ++ Alpha.encode message.securityGroup
    ++ Alpha.encode message.asset
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 4 message.securityId
    ++ Alpha.encode message.securityType
    ++ Alpha.encode message.cfiCode
    ++ MaturityMonthYear.encode message.maturityMonthYear
    ++ Alpha.encode message.currency
    ++ Alpha.encode message.securitySubType
    ++ Alpha.encode message.userDefinedInstrument
    ++ Alpha.encode message.matchAlgorithm
    ++ encodeUIntLE 4 message.minTradeVol
    ++ encodeUIntLE 4 message.maxTradeVol
    ++ encodeUIntLE 8 message.minPriceIncrement
    ++ encodeUIntLE 8 message.displayFactor
    ++ encodeUInt 1 message.priceDisplayFormat
    ++ encodeUIntLE 8 message.priceRatio
    ++ encodeUInt 1 message.tickRule
    ++ Alpha.encode message.unitOfMeasure
    ++ encodeUIntLE 8 message.tradingReferencePrice
    ++ encodeUIntLE 1 message.settlPriceType
    ++ encodeUIntLE 4 message.openInterestQty
    ++ encodeUIntLE 4 message.clearedVolume
    ++ encodeUIntLE 8 message.highLimitPrice
    ++ encodeUIntLE 8 message.lowLimitPrice
    ++ encodeUIntLE 8 message.maxPriceVariation
    ++ encodeUInt 1 message.mainFraction
    ++ encodeUInt 1 message.subFraction
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.eventsGroup.val.length)
    ++ encodeMany EventsGroup.encode message.eventsGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.feedTypesGroup.val.length)
    ++ encodeMany FeedTypesGroup.encode message.feedTypesGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.instAttribGroup.val.length)
    ++ encodeMany InstAttribGroup.encode message.instAttribGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.lotTypeRulesGroup.val.length)
    ++ encodeMany LotTypeRulesGroup.encode message.lotTypeRulesGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.legacyLegsGroup.val.length)
    ++ encodeMany LegacyLegsGroup.encode message.legacyLegsGroup.val

def decode (bytes : List UInt8) : Option (MdInstrumentDefinitionSpread × List UInt8) := do
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (totNumReportsOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityUpdateAction, bytes) ← SecurityUpdateAction.decode bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (mdSecurityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (applId, bytes) ← decodeUIntLE 2 bytes
  let (marketSegmentId, bytes) ← decodeUInt 1 bytes
  let (underlyingProductOptional, bytes) ← decodeUInt 1 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  let (asset, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (securityType, bytes) ← Alpha.decode 6 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (securitySubType, bytes) ← Alpha.decode 5 bytes
  let (userDefinedInstrument, bytes) ← Alpha.decode 1 bytes
  let (matchAlgorithm, bytes) ← Alpha.decode 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (maxTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (minPriceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (displayFactor, bytes) ← decodeUIntLE 8 bytes
  let (priceDisplayFormat, bytes) ← decodeUInt 1 bytes
  let (priceRatio, bytes) ← decodeUIntLE 8 bytes
  let (tickRule, bytes) ← decodeUInt 1 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 30 bytes
  let (tradingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (openInterestQty, bytes) ← decodeUIntLE 4 bytes
  let (clearedVolume, bytes) ← decodeUIntLE 4 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (mainFraction, bytes) ← decodeUInt 1 bytes
  let (subFraction, bytes) ← decodeUInt 1 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (eventsGroup_, bytes) ← decodeMany EventsGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (feedTypesGroup_, bytes) ← decodeMany FeedTypesGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (instAttribGroup_, bytes) ← decodeMany InstAttribGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (lotTypeRulesGroup_, bytes) ← decodeMany LotTypeRulesGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (legacyLegsGroup_, bytes) ← decodeMany LegacyLegsGroup.decode numInGroup.toNat bytes
  if fits_eventsGroup : eventsGroup_.length < 256 then
    if fits_feedTypesGroup : feedTypesGroup_.length < 256 then
      if fits_instAttribGroup : instAttribGroup_.length < 256 then
        if fits_lotTypeRulesGroup : lotTypeRulesGroup_.length < 256 then
          if fits_legacyLegsGroup : legacyLegsGroup_.length < 256 then
            pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProductOptional, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, maturityMonthYear, currency, securitySubType, userDefinedInstrument, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrement, displayFactor, priceDisplayFormat, priceRatio, tickRule, unitOfMeasure, tradingReferencePrice, settlPriceType, openInterestQty, clearedVolume, highLimitPrice, lowLimitPrice, maxPriceVariation, mainFraction, subFraction, blockLength, eventsGroup := ⟨eventsGroup_, fits_eventsGroup⟩, blockLength, feedTypesGroup := ⟨feedTypesGroup_, fits_feedTypesGroup⟩, blockLength, instAttribGroup := ⟨instAttribGroup_, fits_instAttribGroup⟩, blockLength, lotTypeRulesGroup := ⟨lotTypeRulesGroup_, fits_lotTypeRulesGroup⟩, blockLength, legacyLegsGroup := ⟨legacyLegsGroup_, fits_legacyLegsGroup⟩ }, bytes)
          else none
        else none
      else none
    else none
  else none

@[simp] theorem decode_encode (message : MdInstrumentDefinitionSpread) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_eventsGroup : message.eventsGroup.val.length < 256 := by simpa using message.eventsGroup.length_lt
  have fits_feedTypesGroup : message.feedTypesGroup.val.length < 256 := by simpa using message.feedTypesGroup.length_lt
  have fits_instAttribGroup : message.instAttribGroup.val.length < 256 := by simpa using message.instAttribGroup.length_lt
  have fits_lotTypeRulesGroup : message.lotTypeRulesGroup.val.length < 256 := by simpa using message.lotTypeRulesGroup.length_lt
  have fits_legacyLegsGroup : message.legacyLegsGroup.val.length < 256 := by simpa using message.legacyLegsGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_eventsGroup, fits_eventsGroup, decodeMany_encodeMany EventsGroup.encode EventsGroup.decode EventsGroup.decode_encode, Nat.mod_eq_of_lt fits_feedTypesGroup, fits_feedTypesGroup, decodeMany_encodeMany FeedTypesGroup.encode FeedTypesGroup.decode FeedTypesGroup.decode_encode, Nat.mod_eq_of_lt fits_instAttribGroup, fits_instAttribGroup, decodeMany_encodeMany InstAttribGroup.encode InstAttribGroup.decode InstAttribGroup.decode_encode, Nat.mod_eq_of_lt fits_lotTypeRulesGroup, fits_lotTypeRulesGroup, decodeMany_encodeMany LotTypeRulesGroup.encode LotTypeRulesGroup.decode LotTypeRulesGroup.decode_encode, Nat.mod_eq_of_lt fits_legacyLegsGroup, fits_legacyLegsGroup, decodeMany_encodeMany LegacyLegsGroup.encode LegacyLegsGroup.decode LegacyLegsGroup.decode_encode]

end MdInstrumentDefinitionSpread

/-- Security Status: 30 bytes -/
structure SecurityStatus where
  transactTime : BitVec 64
  securityGroup : Alpha 6
  asset : Alpha 6
  securityIdOptional : BitVec 32
  tradeDate : BitVec 16
  matchEventIndicator : BitVec 8
  securityTradingStatus : BitVec 8
  haltReason : BitVec 8
  securityTradingEvent : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityStatus

def encode (message : SecurityStatus) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ Alpha.encode message.securityGroup
    ++ Alpha.encode message.asset
    ++ encodeUIntLE 4 message.securityIdOptional
    ++ encodeUIntLE 2 message.tradeDate
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUInt 1 message.securityTradingStatus
    ++ encodeUInt 1 message.haltReason
    ++ encodeUInt 1 message.securityTradingEvent

def decode (bytes : List UInt8) : Option (SecurityStatus × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  let (asset, bytes) ← Alpha.decode 6 bytes
  let (securityIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (haltReason, bytes) ← decodeUInt 1 bytes
  let (securityTradingEvent, bytes) ← decodeUInt 1 bytes
  pure ({ transactTime, securityGroup, asset, securityIdOptional, tradeDate, matchEventIndicator, securityTradingStatus, haltReason, securityTradingEvent }, bytes)

@[simp] theorem encode_length (message : SecurityStatus) : (encode message).length = 30 := by
  simp [encode]

theorem encode_length_pos (message : SecurityStatus) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SecurityStatus) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end SecurityStatus

/-- Incremental Refresh Book Group: 32 bytes -/
structure IncrementalRefreshBookGroup where
  mdEntryPxOptional : BitVec 64
  mdEntrySizeOptional : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  numberOfOrders : BitVec 32
  mdPriceLevel : BitVec 8
  mdUpdateAction : BitVec 8
  mdEntryTypeBook : MdEntryTypeBook
  padding5 : Alpha 5
  deriving DecidableEq, Repr

namespace IncrementalRefreshBookGroup

def encode (message : IncrementalRefreshBookGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxOptional
    ++ encodeUIntLE 4 message.mdEntrySizeOptional
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 4 message.numberOfOrders
    ++ encodeUInt 1 message.mdPriceLevel
    ++ encodeUInt 1 message.mdUpdateAction
    ++ MdEntryTypeBook.encode message.mdEntryTypeBook
    ++ Alpha.encode message.padding5

def decode (bytes : List UInt8) : Option (IncrementalRefreshBookGroup × List UInt8) := do
  let (mdEntryPxOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (mdPriceLevel, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryTypeBook, bytes) ← MdEntryTypeBook.decode bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  pure ({ mdEntryPxOptional, mdEntrySizeOptional, securityId, rptSeq, numberOfOrders, mdPriceLevel, mdUpdateAction, mdEntryTypeBook, padding5 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshBookGroup) : (encode message).length = 32 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshBookGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshBookGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshBookGroup

/-- Md Incremental Refresh Book -/
structure MdIncrementalRefreshBook where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  incrementalRefreshBookGroup : Bounded 1 IncrementalRefreshBookGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshBook

def encode (message : MdIncrementalRefreshBook) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshBookGroup.val.length)
    ++ encodeMany IncrementalRefreshBookGroup.encode message.incrementalRefreshBookGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshBook × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshBookGroup_, bytes) ← decodeMany IncrementalRefreshBookGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshBookGroup : incrementalRefreshBookGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, padding2, blockLength, incrementalRefreshBookGroup := ⟨incrementalRefreshBookGroup_, fits_incrementalRefreshBookGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshBook) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshBookGroup : message.incrementalRefreshBookGroup.val.length < 256 := by simpa using message.incrementalRefreshBookGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshBookGroup, fits_incrementalRefreshBookGroup, decodeMany_encodeMany IncrementalRefreshBookGroup.encode IncrementalRefreshBookGroup.decode IncrementalRefreshBookGroup.decode_encode]

end MdIncrementalRefreshBook

/-- Incremental Refresh Daily Statistics Group: 32 bytes -/
structure IncrementalRefreshDailyStatisticsGroup where
  mdEntryPxOptional : BitVec 64
  mdEntrySizeOptional : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  tradingReferenceDate : BitVec 16
  settlPriceType : BitVec 8
  mdUpdateAction : BitVec 8
  mdEntryTypeDailyStatistics : MdEntryTypeDailyStatistics
  padding7 : Alpha 7
  deriving DecidableEq, Repr

namespace IncrementalRefreshDailyStatisticsGroup

def encode (message : IncrementalRefreshDailyStatisticsGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxOptional
    ++ encodeUIntLE 4 message.mdEntrySizeOptional
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 2 message.tradingReferenceDate
    ++ encodeUIntLE 1 message.settlPriceType
    ++ encodeUInt 1 message.mdUpdateAction
    ++ MdEntryTypeDailyStatistics.encode message.mdEntryTypeDailyStatistics
    ++ Alpha.encode message.padding7

def decode (bytes : List UInt8) : Option (IncrementalRefreshDailyStatisticsGroup × List UInt8) := do
  let (mdEntryPxOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryTypeDailyStatistics, bytes) ← MdEntryTypeDailyStatistics.decode bytes
  let (padding7, bytes) ← Alpha.decode 7 bytes
  pure ({ mdEntryPxOptional, mdEntrySizeOptional, securityId, rptSeq, tradingReferenceDate, settlPriceType, mdUpdateAction, mdEntryTypeDailyStatistics, padding7 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshDailyStatisticsGroup) : (encode message).length = 32 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshDailyStatisticsGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshDailyStatisticsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshDailyStatisticsGroup

/-- Md Incremental Refresh Daily Statistics -/
structure MdIncrementalRefreshDailyStatistics where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  incrementalRefreshDailyStatisticsGroup : Bounded 1 IncrementalRefreshDailyStatisticsGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshDailyStatistics

def encode (message : MdIncrementalRefreshDailyStatistics) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshDailyStatisticsGroup.val.length)
    ++ encodeMany IncrementalRefreshDailyStatisticsGroup.encode message.incrementalRefreshDailyStatisticsGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshDailyStatistics × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshDailyStatisticsGroup_, bytes) ← decodeMany IncrementalRefreshDailyStatisticsGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshDailyStatisticsGroup : incrementalRefreshDailyStatisticsGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, padding2, blockLength, incrementalRefreshDailyStatisticsGroup := ⟨incrementalRefreshDailyStatisticsGroup_, fits_incrementalRefreshDailyStatisticsGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshDailyStatistics) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshDailyStatisticsGroup : message.incrementalRefreshDailyStatisticsGroup.val.length < 256 := by simpa using message.incrementalRefreshDailyStatisticsGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshDailyStatisticsGroup, fits_incrementalRefreshDailyStatisticsGroup, decodeMany_encodeMany IncrementalRefreshDailyStatisticsGroup.encode IncrementalRefreshDailyStatisticsGroup.decode IncrementalRefreshDailyStatisticsGroup.decode_encode]

end MdIncrementalRefreshDailyStatistics

/-- Incremental Refresh Limits Banding Group: 32 bytes -/
structure IncrementalRefreshLimitsBandingGroup where
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  securityId : BitVec 32
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace IncrementalRefreshLimitsBandingGroup

def encode (message : IncrementalRefreshLimitsBandingGroup) : List UInt8 :=
  encodeUIntLE 8 message.highLimitPrice
    ++ encodeUIntLE 8 message.lowLimitPrice
    ++ encodeUIntLE 8 message.maxPriceVariation
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq

def decode (bytes : List UInt8) : Option (IncrementalRefreshLimitsBandingGroup × List UInt8) := do
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ highLimitPrice, lowLimitPrice, maxPriceVariation, securityId, rptSeq }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshLimitsBandingGroup) : (encode message).length = 32 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshLimitsBandingGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshLimitsBandingGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshLimitsBandingGroup

/-- Md Incremental Refresh Limits Banding -/
structure MdIncrementalRefreshLimitsBanding where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  incrementalRefreshLimitsBandingGroup : Bounded 1 IncrementalRefreshLimitsBandingGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshLimitsBanding

def encode (message : MdIncrementalRefreshLimitsBanding) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshLimitsBandingGroup.val.length)
    ++ encodeMany IncrementalRefreshLimitsBandingGroup.encode message.incrementalRefreshLimitsBandingGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshLimitsBanding × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshLimitsBandingGroup_, bytes) ← decodeMany IncrementalRefreshLimitsBandingGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshLimitsBandingGroup : incrementalRefreshLimitsBandingGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, padding2, blockLength, incrementalRefreshLimitsBandingGroup := ⟨incrementalRefreshLimitsBandingGroup_, fits_incrementalRefreshLimitsBandingGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshLimitsBanding) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshLimitsBandingGroup : message.incrementalRefreshLimitsBandingGroup.val.length < 256 := by simpa using message.incrementalRefreshLimitsBandingGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshLimitsBandingGroup, fits_incrementalRefreshLimitsBandingGroup, decodeMany_encodeMany IncrementalRefreshLimitsBandingGroup.encode IncrementalRefreshLimitsBandingGroup.decode IncrementalRefreshLimitsBandingGroup.decode_encode]

end MdIncrementalRefreshLimitsBanding

/-- Incremental Refresh Session Statistics Group: 24 bytes -/
structure IncrementalRefreshSessionStatisticsGroup where
  mdEntryPx : BitVec 64
  securityId : BitVec 32
  rptSeq : BitVec 32
  openCloseSettlFlag : BitVec 8
  mdUpdateAction : BitVec 8
  mdEntryTypeStatistics : MdEntryTypeStatistics
  padding5 : Alpha 5
  deriving DecidableEq, Repr

namespace IncrementalRefreshSessionStatisticsGroup

def encode (message : IncrementalRefreshSessionStatisticsGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPx
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ encodeUInt 1 message.mdUpdateAction
    ++ MdEntryTypeStatistics.encode message.mdEntryTypeStatistics
    ++ Alpha.encode message.padding5

def decode (bytes : List UInt8) : Option (IncrementalRefreshSessionStatisticsGroup × List UInt8) := do
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryTypeStatistics, bytes) ← MdEntryTypeStatistics.decode bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  pure ({ mdEntryPx, securityId, rptSeq, openCloseSettlFlag, mdUpdateAction, mdEntryTypeStatistics, padding5 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshSessionStatisticsGroup) : (encode message).length = 24 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshSessionStatisticsGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshSessionStatisticsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshSessionStatisticsGroup

/-- Md Incremental Refresh Session Statistics -/
structure MdIncrementalRefreshSessionStatistics where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  incrementalRefreshSessionStatisticsGroup : Bounded 1 IncrementalRefreshSessionStatisticsGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshSessionStatistics

def encode (message : MdIncrementalRefreshSessionStatistics) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshSessionStatisticsGroup.val.length)
    ++ encodeMany IncrementalRefreshSessionStatisticsGroup.encode message.incrementalRefreshSessionStatisticsGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshSessionStatistics × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshSessionStatisticsGroup_, bytes) ← decodeMany IncrementalRefreshSessionStatisticsGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshSessionStatisticsGroup : incrementalRefreshSessionStatisticsGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, padding2, blockLength, incrementalRefreshSessionStatisticsGroup := ⟨incrementalRefreshSessionStatisticsGroup_, fits_incrementalRefreshSessionStatisticsGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshSessionStatistics) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshSessionStatisticsGroup : message.incrementalRefreshSessionStatisticsGroup.val.length < 256 := by simpa using message.incrementalRefreshSessionStatisticsGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshSessionStatisticsGroup, fits_incrementalRefreshSessionStatisticsGroup, decodeMany_encodeMany IncrementalRefreshSessionStatisticsGroup.encode IncrementalRefreshSessionStatisticsGroup.decode IncrementalRefreshSessionStatisticsGroup.decode_encode]

end MdIncrementalRefreshSessionStatistics

/-- Incremental Refresh Trade Group: 32 bytes -/
structure IncrementalRefreshTradeGroup where
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  numberOfOrders : BitVec 32
  tradeId : BitVec 32
  aggressorSide : BitVec 8
  mdUpdateAction : BitVec 8
  padding2 : Alpha 2
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeGroup

def encode (message : IncrementalRefreshTradeGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPx
    ++ encodeUIntLE 4 message.mdEntrySize
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 4 message.numberOfOrders
    ++ encodeUIntLE 4 message.tradeId
    ++ encodeUInt 1 message.aggressorSide
    ++ encodeUInt 1 message.mdUpdateAction
    ++ Alpha.encode message.padding2

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeGroup × List UInt8) := do
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  pure ({ mdEntryPx, mdEntrySize, securityId, rptSeq, numberOfOrders, tradeId, aggressorSide, mdUpdateAction, padding2 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshTradeGroup) : (encode message).length = 32 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshTradeGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshTradeGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshTradeGroup

/-- Md Incremental Refresh Trade -/
structure MdIncrementalRefreshTrade where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  incrementalRefreshTradeGroup : Bounded 1 IncrementalRefreshTradeGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshTrade

def encode (message : MdIncrementalRefreshTrade) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshTradeGroup.val.length)
    ++ encodeMany IncrementalRefreshTradeGroup.encode message.incrementalRefreshTradeGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshTrade × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTradeGroup_, bytes) ← decodeMany IncrementalRefreshTradeGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshTradeGroup : incrementalRefreshTradeGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, padding2, blockLength, incrementalRefreshTradeGroup := ⟨incrementalRefreshTradeGroup_, fits_incrementalRefreshTradeGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshTrade) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshTradeGroup : message.incrementalRefreshTradeGroup.val.length < 256 := by simpa using message.incrementalRefreshTradeGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshTradeGroup, fits_incrementalRefreshTradeGroup, decodeMany_encodeMany IncrementalRefreshTradeGroup.encode IncrementalRefreshTradeGroup.decode IncrementalRefreshTradeGroup.decode_encode]

end MdIncrementalRefreshTrade

/-- Incremental Refresh Volume Group: 16 bytes -/
structure IncrementalRefreshVolumeGroup where
  mdEntrySize : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  mdUpdateAction : BitVec 8
  padding3 : Alpha 3
  deriving DecidableEq, Repr

namespace IncrementalRefreshVolumeGroup

def encode (message : IncrementalRefreshVolumeGroup) : List UInt8 :=
  encodeUIntLE 4 message.mdEntrySize
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUInt 1 message.mdUpdateAction
    ++ Alpha.encode message.padding3

def decode (bytes : List UInt8) : Option (IncrementalRefreshVolumeGroup × List UInt8) := do
  let (mdEntrySize, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (padding3, bytes) ← Alpha.decode 3 bytes
  pure ({ mdEntrySize, securityId, rptSeq, mdUpdateAction, padding3 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshVolumeGroup) : (encode message).length = 16 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshVolumeGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshVolumeGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshVolumeGroup

/-- Md Incremental Refresh Volume -/
structure MdIncrementalRefreshVolume where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  incrementalRefreshVolumeGroup : Bounded 1 IncrementalRefreshVolumeGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshVolume

def encode (message : MdIncrementalRefreshVolume) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshVolumeGroup.val.length)
    ++ encodeMany IncrementalRefreshVolumeGroup.encode message.incrementalRefreshVolumeGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshVolume × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshVolumeGroup_, bytes) ← decodeMany IncrementalRefreshVolumeGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshVolumeGroup : incrementalRefreshVolumeGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, padding2, blockLength, incrementalRefreshVolumeGroup := ⟨incrementalRefreshVolumeGroup_, fits_incrementalRefreshVolumeGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshVolume) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshVolumeGroup : message.incrementalRefreshVolumeGroup.val.length < 256 := by simpa using message.incrementalRefreshVolumeGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshVolumeGroup, fits_incrementalRefreshVolumeGroup, decodeMany_encodeMany IncrementalRefreshVolumeGroup.encode IncrementalRefreshVolumeGroup.decode IncrementalRefreshVolumeGroup.decode_encode]

end MdIncrementalRefreshVolume

/-- Snapshot Full Refresh Group: 22 bytes -/
structure SnapshotFullRefreshGroup where
  mdEntryPxOptional : BitVec 64
  mdEntrySizeOptional : BitVec 32
  numberOfOrders : BitVec 32
  mdPriceLevelOptional : BitVec 8
  tradingReferenceDate : BitVec 16
  openCloseSettlFlag : BitVec 8
  settlPriceType : BitVec 8
  mdEntryType : MdEntryType
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshGroup

def encode (message : SnapshotFullRefreshGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxOptional
    ++ encodeUIntLE 4 message.mdEntrySizeOptional
    ++ encodeUIntLE 4 message.numberOfOrders
    ++ encodeUInt 1 message.mdPriceLevelOptional
    ++ encodeUIntLE 2 message.tradingReferenceDate
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ encodeUIntLE 1 message.settlPriceType
    ++ MdEntryType.encode message.mdEntryType

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshGroup × List UInt8) := do
  let (mdEntryPxOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (mdPriceLevelOptional, bytes) ← decodeUInt 1 bytes
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  pure ({ mdEntryPxOptional, mdEntrySizeOptional, numberOfOrders, mdPriceLevelOptional, tradingReferenceDate, openCloseSettlFlag, settlPriceType, mdEntryType }, bytes)

@[simp] theorem encode_length (message : SnapshotFullRefreshGroup) : (encode message).length = 22 := by
  simp [encode]

theorem encode_length_pos (message : SnapshotFullRefreshGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SnapshotFullRefreshGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end SnapshotFullRefreshGroup

/-- Snapshot Full Refresh -/
structure SnapshotFullRefresh where
  lastMsgSeqNumProcessed : BitVec 32
  totNumReports : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  transactTime : BitVec 64
  lastUpdateTime : BitVec 64
  tradeDate : BitVec 16
  mdSecurityTradingStatus : BitVec 8
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  blockLength : BitVec 16
  snapshotFullRefreshGroup : Bounded 1 SnapshotFullRefreshGroup
  deriving DecidableEq, Repr

namespace SnapshotFullRefresh

def encode (message : SnapshotFullRefresh) : List UInt8 :=
  encodeUIntLE 4 message.lastMsgSeqNumProcessed
    ++ encodeUIntLE 4 message.totNumReports
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.lastUpdateTime
    ++ encodeUIntLE 2 message.tradeDate
    ++ encodeUInt 1 message.mdSecurityTradingStatus
    ++ encodeUIntLE 8 message.highLimitPrice
    ++ encodeUIntLE 8 message.lowLimitPrice
    ++ encodeUIntLE 8 message.maxPriceVariation
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.snapshotFullRefreshGroup.val.length)
    ++ encodeMany SnapshotFullRefreshGroup.encode message.snapshotFullRefreshGroup.val

def decode (bytes : List UInt8) : Option (SnapshotFullRefresh × List UInt8) := do
  let (lastMsgSeqNumProcessed, bytes) ← decodeUIntLE 4 bytes
  let (totNumReports, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (mdSecurityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotFullRefreshGroup_, bytes) ← decodeMany SnapshotFullRefreshGroup.decode numInGroup.toNat bytes
  if fits_snapshotFullRefreshGroup : snapshotFullRefreshGroup_.length < 256 then
    pure ({ lastMsgSeqNumProcessed, totNumReports, securityId, rptSeq, transactTime, lastUpdateTime, tradeDate, mdSecurityTradingStatus, highLimitPrice, lowLimitPrice, maxPriceVariation, blockLength, snapshotFullRefreshGroup := ⟨snapshotFullRefreshGroup_, fits_snapshotFullRefreshGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : SnapshotFullRefresh) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_snapshotFullRefreshGroup : message.snapshotFullRefreshGroup.val.length < 256 := by simpa using message.snapshotFullRefreshGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_snapshotFullRefreshGroup, fits_snapshotFullRefreshGroup, decodeMany_encodeMany SnapshotFullRefreshGroup.encode SnapshotFullRefreshGroup.decode SnapshotFullRefreshGroup.decode_encode]

end SnapshotFullRefresh

/-- Related Sym Group: 32 bytes -/
structure RelatedSymGroup where
  symbol : Alpha 20
  securityId : BitVec 32
  orderQty : BitVec 32
  quoteType : BitVec 8
  side : BitVec 8
  padding2 : Alpha 2
  deriving DecidableEq, Repr

namespace RelatedSymGroup

def encode (message : RelatedSymGroup) : List UInt8 :=
  Alpha.encode message.symbol
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUInt 1 message.quoteType
    ++ encodeUInt 1 message.side
    ++ Alpha.encode message.padding2

def decode (bytes : List UInt8) : Option (RelatedSymGroup × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  pure ({ symbol, securityId, orderQty, quoteType, side, padding2 }, bytes)

@[simp] theorem encode_length (message : RelatedSymGroup) : (encode message).length = 32 := by
  simp [encode]

theorem encode_length_pos (message : RelatedSymGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : RelatedSymGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end RelatedSymGroup

/-- Quote Request -/
structure QuoteRequest where
  transactTime : BitVec 64
  quoteReqId : Alpha 23
  matchEventIndicator : BitVec 8
  padding3 : Alpha 3
  blockLength : BitVec 16
  relatedSymGroup : Bounded 1 RelatedSymGroup
  deriving DecidableEq, Repr

namespace QuoteRequest

def encode (message : QuoteRequest) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ Alpha.encode message.quoteReqId
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding3
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.relatedSymGroup.val.length)
    ++ encodeMany RelatedSymGroup.encode message.relatedSymGroup.val

def decode (bytes : List UInt8) : Option (QuoteRequest × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteReqId, bytes) ← Alpha.decode 23 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding3, bytes) ← Alpha.decode 3 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (relatedSymGroup_, bytes) ← decodeMany RelatedSymGroup.decode numInGroup.toNat bytes
  if fits_relatedSymGroup : relatedSymGroup_.length < 256 then
    pure ({ transactTime, quoteReqId, matchEventIndicator, padding3, blockLength, relatedSymGroup := ⟨relatedSymGroup_, fits_relatedSymGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : QuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_relatedSymGroup : message.relatedSymGroup.val.length < 256 := by simpa using message.relatedSymGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_relatedSymGroup, fits_relatedSymGroup, decodeMany_encodeMany RelatedSymGroup.encode RelatedSymGroup.decode RelatedSymGroup.decode_encode]

end QuoteRequest

/-- Option Underlyings Group: 24 bytes -/
structure OptionUnderlyingsGroup where
  underlyingSecurityId : BitVec 32
  underlyingSymbol : Alpha 20
  deriving DecidableEq, Repr

namespace OptionUnderlyingsGroup

def encode (message : OptionUnderlyingsGroup) : List UInt8 :=
  encodeUIntLE 4 message.underlyingSecurityId
    ++ Alpha.encode message.underlyingSymbol

def decode (bytes : List UInt8) : Option (OptionUnderlyingsGroup × List UInt8) := do
  let (underlyingSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 20 bytes
  pure ({ underlyingSecurityId, underlyingSymbol }, bytes)

@[simp] theorem encode_length (message : OptionUnderlyingsGroup) : (encode message).length = 24 := by
  simp [encode]

theorem encode_length_pos (message : OptionUnderlyingsGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : OptionUnderlyingsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end OptionUnderlyingsGroup

/-- Md Instrument Definition Option -/
structure MdInstrumentDefinitionOption where
  matchEventIndicator : BitVec 8
  totNumReportsOptional : BitVec 32
  securityUpdateAction : SecurityUpdateAction
  lastUpdateTime : BitVec 64
  mdSecurityTradingStatus : BitVec 8
  applId : BitVec 16
  marketSegmentId : BitVec 8
  underlyingProduct : BitVec 8
  securityExchange : Alpha 4
  securityGroup : Alpha 6
  asset : Alpha 6
  symbol : Alpha 20
  securityId : BitVec 32
  securityType : Alpha 6
  cfiCode : Alpha 6
  putOrCall : BitVec 8
  maturityMonthYear : MaturityMonthYear
  currency : Alpha 3
  strikePrice : BitVec 64
  strikeCurrency : Alpha 3
  settlCurrency : Alpha 3
  minCabPrice : BitVec 64
  matchAlgorithm : Alpha 1
  minTradeVol : BitVec 32
  maxTradeVol : BitVec 32
  minPriceIncrementOptional : BitVec 64
  minPriceIncrementAmount : BitVec 64
  displayFactor : BitVec 64
  tickRule : BitVec 8
  mainFraction : BitVec 8
  subFraction : BitVec 8
  priceDisplayFormat : BitVec 8
  unitOfMeasure : Alpha 30
  unitOfMeasureQty : BitVec 64
  tradingReferencePrice : BitVec 64
  settlPriceType : BitVec 8
  clearedVolume : BitVec 32
  openInterestQty : BitVec 32
  lowLimitPrice : BitVec 64
  highLimitPrice : BitVec 64
  userDefinedInstrument : Alpha 1
  blockLength : BitVec 16
  eventsGroup : Bounded 1 EventsGroup
  blockLength : BitVec 16
  feedTypesGroup : Bounded 1 FeedTypesGroup
  blockLength : BitVec 16
  instAttribGroup : Bounded 1 InstAttribGroup
  blockLength : BitVec 16
  lotTypeRulesGroup : Bounded 1 LotTypeRulesGroup
  blockLength : BitVec 16
  optionUnderlyingsGroup : Bounded 1 OptionUnderlyingsGroup
  deriving DecidableEq, Repr

namespace MdInstrumentDefinitionOption

def encode (message : MdInstrumentDefinitionOption) : List UInt8 :=
  encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 4 message.totNumReportsOptional
    ++ SecurityUpdateAction.encode message.securityUpdateAction
    ++ encodeUIntLE 8 message.lastUpdateTime
    ++ encodeUInt 1 message.mdSecurityTradingStatus
    ++ encodeUIntLE 2 message.applId
    ++ encodeUInt 1 message.marketSegmentId
    ++ encodeUInt 1 message.underlyingProduct
    ++ Alpha.encode message.securityExchange
    ++ Alpha.encode message.securityGroup
    ++ Alpha.encode message.asset
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 4 message.securityId
    ++ Alpha.encode message.securityType
    ++ Alpha.encode message.cfiCode
    ++ encodeUInt 1 message.putOrCall
    ++ MaturityMonthYear.encode message.maturityMonthYear
    ++ Alpha.encode message.currency
    ++ encodeUIntLE 8 message.strikePrice
    ++ Alpha.encode message.strikeCurrency
    ++ Alpha.encode message.settlCurrency
    ++ encodeUIntLE 8 message.minCabPrice
    ++ Alpha.encode message.matchAlgorithm
    ++ encodeUIntLE 4 message.minTradeVol
    ++ encodeUIntLE 4 message.maxTradeVol
    ++ encodeUIntLE 8 message.minPriceIncrementOptional
    ++ encodeUIntLE 8 message.minPriceIncrementAmount
    ++ encodeUIntLE 8 message.displayFactor
    ++ encodeUInt 1 message.tickRule
    ++ encodeUInt 1 message.mainFraction
    ++ encodeUInt 1 message.subFraction
    ++ encodeUInt 1 message.priceDisplayFormat
    ++ Alpha.encode message.unitOfMeasure
    ++ encodeUIntLE 8 message.unitOfMeasureQty
    ++ encodeUIntLE 8 message.tradingReferencePrice
    ++ encodeUIntLE 1 message.settlPriceType
    ++ encodeUIntLE 4 message.clearedVolume
    ++ encodeUIntLE 4 message.openInterestQty
    ++ encodeUIntLE 8 message.lowLimitPrice
    ++ encodeUIntLE 8 message.highLimitPrice
    ++ Alpha.encode message.userDefinedInstrument
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.eventsGroup.val.length)
    ++ encodeMany EventsGroup.encode message.eventsGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.feedTypesGroup.val.length)
    ++ encodeMany FeedTypesGroup.encode message.feedTypesGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.instAttribGroup.val.length)
    ++ encodeMany InstAttribGroup.encode message.instAttribGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.lotTypeRulesGroup.val.length)
    ++ encodeMany LotTypeRulesGroup.encode message.lotTypeRulesGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.optionUnderlyingsGroup.val.length)
    ++ encodeMany OptionUnderlyingsGroup.encode message.optionUnderlyingsGroup.val

def decode (bytes : List UInt8) : Option (MdInstrumentDefinitionOption × List UInt8) := do
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (totNumReportsOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityUpdateAction, bytes) ← SecurityUpdateAction.decode bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (mdSecurityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (applId, bytes) ← decodeUIntLE 2 bytes
  let (marketSegmentId, bytes) ← decodeUInt 1 bytes
  let (underlyingProduct, bytes) ← decodeUInt 1 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  let (asset, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (securityType, bytes) ← Alpha.decode 6 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (strikeCurrency, bytes) ← Alpha.decode 3 bytes
  let (settlCurrency, bytes) ← Alpha.decode 3 bytes
  let (minCabPrice, bytes) ← decodeUIntLE 8 bytes
  let (matchAlgorithm, bytes) ← Alpha.decode 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (maxTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (minPriceIncrementOptional, bytes) ← decodeUIntLE 8 bytes
  let (minPriceIncrementAmount, bytes) ← decodeUIntLE 8 bytes
  let (displayFactor, bytes) ← decodeUIntLE 8 bytes
  let (tickRule, bytes) ← decodeUInt 1 bytes
  let (mainFraction, bytes) ← decodeUInt 1 bytes
  let (subFraction, bytes) ← decodeUInt 1 bytes
  let (priceDisplayFormat, bytes) ← decodeUInt 1 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 30 bytes
  let (unitOfMeasureQty, bytes) ← decodeUIntLE 8 bytes
  let (tradingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (clearedVolume, bytes) ← decodeUIntLE 4 bytes
  let (openInterestQty, bytes) ← decodeUIntLE 4 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (userDefinedInstrument, bytes) ← Alpha.decode 1 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (eventsGroup_, bytes) ← decodeMany EventsGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (feedTypesGroup_, bytes) ← decodeMany FeedTypesGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (instAttribGroup_, bytes) ← decodeMany InstAttribGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (lotTypeRulesGroup_, bytes) ← decodeMany LotTypeRulesGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (optionUnderlyingsGroup_, bytes) ← decodeMany OptionUnderlyingsGroup.decode numInGroup.toNat bytes
  if fits_eventsGroup : eventsGroup_.length < 256 then
    if fits_feedTypesGroup : feedTypesGroup_.length < 256 then
      if fits_instAttribGroup : instAttribGroup_.length < 256 then
        if fits_lotTypeRulesGroup : lotTypeRulesGroup_.length < 256 then
          if fits_optionUnderlyingsGroup : optionUnderlyingsGroup_.length < 256 then
            pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, putOrCall, maturityMonthYear, currency, strikePrice, strikeCurrency, settlCurrency, minCabPrice, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementOptional, minPriceIncrementAmount, displayFactor, tickRule, mainFraction, subFraction, priceDisplayFormat, unitOfMeasure, unitOfMeasureQty, tradingReferencePrice, settlPriceType, clearedVolume, openInterestQty, lowLimitPrice, highLimitPrice, userDefinedInstrument, blockLength, eventsGroup := ⟨eventsGroup_, fits_eventsGroup⟩, blockLength, feedTypesGroup := ⟨feedTypesGroup_, fits_feedTypesGroup⟩, blockLength, instAttribGroup := ⟨instAttribGroup_, fits_instAttribGroup⟩, blockLength, lotTypeRulesGroup := ⟨lotTypeRulesGroup_, fits_lotTypeRulesGroup⟩, blockLength, optionUnderlyingsGroup := ⟨optionUnderlyingsGroup_, fits_optionUnderlyingsGroup⟩ }, bytes)
          else none
        else none
      else none
    else none
  else none

@[simp] theorem decode_encode (message : MdInstrumentDefinitionOption) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_eventsGroup : message.eventsGroup.val.length < 256 := by simpa using message.eventsGroup.length_lt
  have fits_feedTypesGroup : message.feedTypesGroup.val.length < 256 := by simpa using message.feedTypesGroup.length_lt
  have fits_instAttribGroup : message.instAttribGroup.val.length < 256 := by simpa using message.instAttribGroup.length_lt
  have fits_lotTypeRulesGroup : message.lotTypeRulesGroup.val.length < 256 := by simpa using message.lotTypeRulesGroup.length_lt
  have fits_optionUnderlyingsGroup : message.optionUnderlyingsGroup.val.length < 256 := by simpa using message.optionUnderlyingsGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_eventsGroup, fits_eventsGroup, decodeMany_encodeMany EventsGroup.encode EventsGroup.decode EventsGroup.decode_encode, Nat.mod_eq_of_lt fits_feedTypesGroup, fits_feedTypesGroup, decodeMany_encodeMany FeedTypesGroup.encode FeedTypesGroup.decode FeedTypesGroup.decode_encode, Nat.mod_eq_of_lt fits_instAttribGroup, fits_instAttribGroup, decodeMany_encodeMany InstAttribGroup.encode InstAttribGroup.decode InstAttribGroup.decode_encode, Nat.mod_eq_of_lt fits_lotTypeRulesGroup, fits_lotTypeRulesGroup, decodeMany_encodeMany LotTypeRulesGroup.encode LotTypeRulesGroup.decode LotTypeRulesGroup.decode_encode, Nat.mod_eq_of_lt fits_optionUnderlyingsGroup, fits_optionUnderlyingsGroup, decodeMany_encodeMany OptionUnderlyingsGroup.encode OptionUnderlyingsGroup.decode OptionUnderlyingsGroup.decode_encode]

end MdInstrumentDefinitionOption

/-- Incremental Refresh Trade Summary Group: 32 bytes -/
structure IncrementalRefreshTradeSummaryGroup where
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  numberOfOrders : BitVec 32
  aggressorSide : BitVec 8
  mdUpdateAction : BitVec 8
  padding6 : Alpha 6
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeSummaryGroup

def encode (message : IncrementalRefreshTradeSummaryGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPx
    ++ encodeUIntLE 4 message.mdEntrySize
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 4 message.numberOfOrders
    ++ encodeUInt 1 message.aggressorSide
    ++ encodeUInt 1 message.mdUpdateAction
    ++ Alpha.encode message.padding6

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeSummaryGroup × List UInt8) := do
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (padding6, bytes) ← Alpha.decode 6 bytes
  pure ({ mdEntryPx, mdEntrySize, securityId, rptSeq, numberOfOrders, aggressorSide, mdUpdateAction, padding6 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshTradeSummaryGroup) : (encode message).length = 32 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshTradeSummaryGroup

/-- Incremental Refresh Trade Summary Order Id Group: 16 bytes -/
structure IncrementalRefreshTradeSummaryOrderIdGroup where
  orderId : BitVec 64
  lastQty : BitVec 32
  padding4 : Alpha 4
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeSummaryOrderIdGroup

def encode (message : IncrementalRefreshTradeSummaryOrderIdGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 4 message.lastQty
    ++ Alpha.encode message.padding4

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeSummaryOrderIdGroup × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (padding4, bytes) ← Alpha.decode 4 bytes
  pure ({ orderId, lastQty, padding4 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshTradeSummaryOrderIdGroup) : (encode message).length = 16 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryOrderIdGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryOrderIdGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshTradeSummaryOrderIdGroup

/-- Md Incremental Refresh Trade Summary -/
structure MdIncrementalRefreshTradeSummary where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  incrementalRefreshTradeSummaryGroup : Bounded 1 IncrementalRefreshTradeSummaryGroup
  blockLength : BitVec 16
  padding5 : Alpha 5
  incrementalRefreshTradeSummaryOrderIdGroup : Bounded 1 IncrementalRefreshTradeSummaryOrderIdGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshTradeSummary

def encode (message : MdIncrementalRefreshTradeSummary) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshTradeSummaryGroup.val.length)
    ++ encodeMany IncrementalRefreshTradeSummaryGroup.encode message.incrementalRefreshTradeSummaryGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ Alpha.encode message.padding5
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshTradeSummaryOrderIdGroup.val.length)
    ++ encodeMany IncrementalRefreshTradeSummaryOrderIdGroup.encode message.incrementalRefreshTradeSummaryOrderIdGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshTradeSummary × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTradeSummaryGroup_, bytes) ← decodeMany IncrementalRefreshTradeSummaryGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTradeSummaryOrderIdGroup_, bytes) ← decodeMany IncrementalRefreshTradeSummaryOrderIdGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshTradeSummaryGroup : incrementalRefreshTradeSummaryGroup_.length < 256 then
    if fits_incrementalRefreshTradeSummaryOrderIdGroup : incrementalRefreshTradeSummaryOrderIdGroup_.length < 256 then
      pure ({ transactTime, matchEventIndicator, padding2, blockLength, incrementalRefreshTradeSummaryGroup := ⟨incrementalRefreshTradeSummaryGroup_, fits_incrementalRefreshTradeSummaryGroup⟩, blockLength, padding5, incrementalRefreshTradeSummaryOrderIdGroup := ⟨incrementalRefreshTradeSummaryOrderIdGroup_, fits_incrementalRefreshTradeSummaryOrderIdGroup⟩ }, bytes)
    else none
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshTradeSummary) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshTradeSummaryGroup : message.incrementalRefreshTradeSummaryGroup.val.length < 256 := by simpa using message.incrementalRefreshTradeSummaryGroup.length_lt
  have fits_incrementalRefreshTradeSummaryOrderIdGroup : message.incrementalRefreshTradeSummaryOrderIdGroup.val.length < 256 := by simpa using message.incrementalRefreshTradeSummaryOrderIdGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshTradeSummaryGroup, fits_incrementalRefreshTradeSummaryGroup, decodeMany_encodeMany IncrementalRefreshTradeSummaryGroup.encode IncrementalRefreshTradeSummaryGroup.decode IncrementalRefreshTradeSummaryGroup.decode_encode, Nat.mod_eq_of_lt fits_incrementalRefreshTradeSummaryOrderIdGroup, fits_incrementalRefreshTradeSummaryOrderIdGroup, decodeMany_encodeMany IncrementalRefreshTradeSummaryOrderIdGroup.encode IncrementalRefreshTradeSummaryOrderIdGroup.decode IncrementalRefreshTradeSummaryOrderIdGroup.decode_encode]

end MdIncrementalRefreshTradeSummary

/-- Negotiation Reject: 70 bytes -/
structure NegotiationReject where
  reason : Alpha 48
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  errorCodes : BitVec 8
  padding5 : Alpha 5
  deriving DecidableEq, Repr

namespace NegotiationReject

def encode (message : NegotiationReject) : List UInt8 :=
  Alpha.encode message.reason
    ++ encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ encodeUInt 1 message.errorCodes
    ++ Alpha.encode message.padding5

def decode (bytes : List UInt8) : Option (NegotiationReject × List UInt8) := do
  let (reason, bytes) ← Alpha.decode 48 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (errorCodes, bytes) ← decodeUInt 1 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  pure ({ reason, uuid, requestTimestamp, errorCodes, padding5 }, bytes)

@[simp] theorem encode_length (message : NegotiationReject) : (encode message).length = 70 := by
  simp [encode]

theorem encode_length_pos (message : NegotiationReject) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : NegotiationReject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end NegotiationReject

/-- Negotiation Response: 22 bytes -/
structure NegotiationResponse where
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  secretKeySecureIdExpiration : BitVec 16
  padding4 : Alpha 4
  deriving DecidableEq, Repr

namespace NegotiationResponse

def encode (message : NegotiationResponse) : List UInt8 :=
  encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ encodeUIntLE 2 message.secretKeySecureIdExpiration
    ++ Alpha.encode message.padding4

def decode (bytes : List UInt8) : Option (NegotiationResponse × List UInt8) := do
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (secretKeySecureIdExpiration, bytes) ← decodeUIntLE 2 bytes
  let (padding4, bytes) ← Alpha.decode 4 bytes
  pure ({ uuid, requestTimestamp, secretKeySecureIdExpiration, padding4 }, bytes)

@[simp] theorem encode_length (message : NegotiationResponse) : (encode message).length = 22 := by
  simp [encode]

theorem encode_length_pos (message : NegotiationResponse) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : NegotiationResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end NegotiationResponse

/-- Terminate: 70 bytes -/
structure Terminate where
  reason : Alpha 48
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  errorCodes : BitVec 8
  padding5 : Alpha 5
  deriving DecidableEq, Repr

namespace Terminate

def encode (message : Terminate) : List UInt8 :=
  Alpha.encode message.reason
    ++ encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ encodeUInt 1 message.errorCodes
    ++ Alpha.encode message.padding5

def decode (bytes : List UInt8) : Option (Terminate × List UInt8) := do
  let (reason, bytes) ← Alpha.decode 48 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (errorCodes, bytes) ← decodeUInt 1 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  pure ({ reason, uuid, requestTimestamp, errorCodes, padding5 }, bytes)

@[simp] theorem encode_length (message : Terminate) : (encode message).length = 70 := by
  simp [encode]

theorem encode_length_pos (message : Terminate) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : Terminate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end Terminate

/-- Request Ack Security Group: 6 bytes -/
structure RequestAckSecurityGroup where
  securityGroup : Alpha 6
  deriving DecidableEq, Repr

namespace RequestAckSecurityGroup

def encode (message : RequestAckSecurityGroup) : List UInt8 :=
  Alpha.encode message.securityGroup

def decode (bytes : List UInt8) : Option (RequestAckSecurityGroup × List UInt8) := do
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  pure ({ securityGroup }, bytes)

@[simp] theorem encode_length (message : RequestAckSecurityGroup) : (encode message).length = 6 := by
  simp [encode]

theorem encode_length_pos (message : RequestAckSecurityGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : RequestAckSecurityGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end RequestAckSecurityGroup

/-- Request Ack Related Symbol Group: 4 bytes -/
structure RequestAckRelatedSymbolGroup where
  securityId : BitVec 32
  deriving DecidableEq, Repr

namespace RequestAckRelatedSymbolGroup

def encode (message : RequestAckRelatedSymbolGroup) : List UInt8 :=
  encodeUIntLE 4 message.securityId

def decode (bytes : List UInt8) : Option (RequestAckRelatedSymbolGroup × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId }, bytes)

@[simp] theorem encode_length (message : RequestAckRelatedSymbolGroup) : (encode message).length = 4 := by
  simp [encode]

theorem encode_length_pos (message : RequestAckRelatedSymbolGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : RequestAckRelatedSymbolGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end RequestAckRelatedSymbolGroup

/-- Request Ack -/
structure RequestAck where
  mdReqId : BitVec 32
  subscriptionReqType : BitVec 8
  mdReqIdStatus : BitVec 8
  blockLength : BitVec 16
  requestAckSecurityGroup : Bounded 1 RequestAckSecurityGroup
  blockLength : BitVec 16
  requestAckRelatedSymbolGroup : Bounded 1 RequestAckRelatedSymbolGroup
  deriving DecidableEq, Repr

namespace RequestAck

def encode (message : RequestAck) : List UInt8 :=
  encodeUIntLE 4 message.mdReqId
    ++ encodeUInt 1 message.subscriptionReqType
    ++ encodeUInt 1 message.mdReqIdStatus
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.requestAckSecurityGroup.val.length)
    ++ encodeMany RequestAckSecurityGroup.encode message.requestAckSecurityGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.requestAckRelatedSymbolGroup.val.length)
    ++ encodeMany RequestAckRelatedSymbolGroup.encode message.requestAckRelatedSymbolGroup.val

def decode (bytes : List UInt8) : Option (RequestAck × List UInt8) := do
  let (mdReqId, bytes) ← decodeUIntLE 4 bytes
  let (subscriptionReqType, bytes) ← decodeUInt 1 bytes
  let (mdReqIdStatus, bytes) ← decodeUInt 1 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (requestAckSecurityGroup_, bytes) ← decodeMany RequestAckSecurityGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (requestAckRelatedSymbolGroup_, bytes) ← decodeMany RequestAckRelatedSymbolGroup.decode numInGroup.toNat bytes
  if fits_requestAckSecurityGroup : requestAckSecurityGroup_.length < 256 then
    if fits_requestAckRelatedSymbolGroup : requestAckRelatedSymbolGroup_.length < 256 then
      pure ({ mdReqId, subscriptionReqType, mdReqIdStatus, blockLength, requestAckSecurityGroup := ⟨requestAckSecurityGroup_, fits_requestAckSecurityGroup⟩, blockLength, requestAckRelatedSymbolGroup := ⟨requestAckRelatedSymbolGroup_, fits_requestAckRelatedSymbolGroup⟩ }, bytes)
    else none
  else none

@[simp] theorem decode_encode (message : RequestAck) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_requestAckSecurityGroup : message.requestAckSecurityGroup.val.length < 256 := by simpa using message.requestAckSecurityGroup.length_lt
  have fits_requestAckRelatedSymbolGroup : message.requestAckRelatedSymbolGroup.val.length < 256 := by simpa using message.requestAckRelatedSymbolGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_requestAckSecurityGroup, fits_requestAckSecurityGroup, decodeMany_encodeMany RequestAckSecurityGroup.encode RequestAckSecurityGroup.decode RequestAckSecurityGroup.decode_encode, Nat.mod_eq_of_lt fits_requestAckRelatedSymbolGroup, fits_requestAckRelatedSymbolGroup, decodeMany_encodeMany RequestAckRelatedSymbolGroup.encode RequestAckRelatedSymbolGroup.decode RequestAckRelatedSymbolGroup.decode_encode]

end RequestAck

/-- Request Reject: 105 bytes -/
structure RequestReject where
  mdReqIdOptional : BitVec 32
  mdReqRejReason : BitVec 8
  text : Alpha 100
  deriving DecidableEq, Repr

namespace RequestReject

def encode (message : RequestReject) : List UInt8 :=
  encodeUIntLE 4 message.mdReqIdOptional
    ++ encodeUInt 1 message.mdReqRejReason
    ++ Alpha.encode message.text

def decode (bytes : List UInt8) : Option (RequestReject × List UInt8) := do
  let (mdReqIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (mdReqRejReason, bytes) ← decodeUInt 1 bytes
  let (text, bytes) ← Alpha.decode 100 bytes
  pure ({ mdReqIdOptional, mdReqRejReason, text }, bytes)

@[simp] theorem encode_length (message : RequestReject) : (encode message).length = 105 := by
  simp [encode]

theorem encode_length_pos (message : RequestReject) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : RequestReject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end RequestReject

/-- Any Server Payload, selected by Template Id -/
inductive ServerPayload where
  | channelReset (message : ChannelReset) -- 4
  | adminHeartbeat (message : AdminHeartbeat) -- 12
  | adminLogin (message : AdminLogin) -- 15
  | adminLogout (message : AdminLogout) -- 16
  | mdInstrumentDefinitionFuture (message : MdInstrumentDefinitionFuture) -- 27
  | mdInstrumentDefinitionSpread (message : MdInstrumentDefinitionSpread) -- 29
  | securityStatus (message : SecurityStatus) -- 30
  | mdIncrementalRefreshBook (message : MdIncrementalRefreshBook) -- 32
  | mdIncrementalRefreshDailyStatistics (message : MdIncrementalRefreshDailyStatistics) -- 33
  | mdIncrementalRefreshLimitsBanding (message : MdIncrementalRefreshLimitsBanding) -- 34
  | mdIncrementalRefreshSessionStatistics (message : MdIncrementalRefreshSessionStatistics) -- 35
  | mdIncrementalRefreshTrade (message : MdIncrementalRefreshTrade) -- 36
  | mdIncrementalRefreshVolume (message : MdIncrementalRefreshVolume) -- 37
  | snapshotFullRefresh (message : SnapshotFullRefresh) -- 38
  | quoteRequest (message : QuoteRequest) -- 39
  | mdInstrumentDefinitionOption (message : MdInstrumentDefinitionOption) -- 41
  | mdIncrementalRefreshTradeSummary (message : MdIncrementalRefreshTradeSummary) -- 42
  | negotiationReject (message : NegotiationReject) -- 201
  | negotiationResponse (message : NegotiationResponse) -- 202
  | terminate (message : Terminate) -- 203
  | requestAck (message : RequestAck) -- 206
  | requestReject (message : RequestReject) -- 207
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Template Id each message is sent under -/
def tag : ServerPayload → BitVec 16
  | .channelReset _ => 4
  | .adminHeartbeat _ => 12
  | .adminLogin _ => 15
  | .adminLogout _ => 16
  | .mdInstrumentDefinitionFuture _ => 27
  | .mdInstrumentDefinitionSpread _ => 29
  | .securityStatus _ => 30
  | .mdIncrementalRefreshBook _ => 32
  | .mdIncrementalRefreshDailyStatistics _ => 33
  | .mdIncrementalRefreshLimitsBanding _ => 34
  | .mdIncrementalRefreshSessionStatistics _ => 35
  | .mdIncrementalRefreshTrade _ => 36
  | .mdIncrementalRefreshVolume _ => 37
  | .snapshotFullRefresh _ => 38
  | .quoteRequest _ => 39
  | .mdInstrumentDefinitionOption _ => 41
  | .mdIncrementalRefreshTradeSummary _ => 42
  | .negotiationReject _ => 201
  | .negotiationResponse _ => 202
  | .terminate _ => 203
  | .requestAck _ => 206
  | .requestReject _ => 207

def encode : ServerPayload → List UInt8
  | .channelReset message => ChannelReset.encode message
  | .adminHeartbeat message => AdminHeartbeat.encode message
  | .adminLogin message => AdminLogin.encode message
  | .adminLogout message => AdminLogout.encode message
  | .mdInstrumentDefinitionFuture message => MdInstrumentDefinitionFuture.encode message
  | .mdInstrumentDefinitionSpread message => MdInstrumentDefinitionSpread.encode message
  | .securityStatus message => SecurityStatus.encode message
  | .mdIncrementalRefreshBook message => MdIncrementalRefreshBook.encode message
  | .mdIncrementalRefreshDailyStatistics message => MdIncrementalRefreshDailyStatistics.encode message
  | .mdIncrementalRefreshLimitsBanding message => MdIncrementalRefreshLimitsBanding.encode message
  | .mdIncrementalRefreshSessionStatistics message => MdIncrementalRefreshSessionStatistics.encode message
  | .mdIncrementalRefreshTrade message => MdIncrementalRefreshTrade.encode message
  | .mdIncrementalRefreshVolume message => MdIncrementalRefreshVolume.encode message
  | .snapshotFullRefresh message => SnapshotFullRefresh.encode message
  | .quoteRequest message => QuoteRequest.encode message
  | .mdInstrumentDefinitionOption message => MdInstrumentDefinitionOption.encode message
  | .mdIncrementalRefreshTradeSummary message => MdIncrementalRefreshTradeSummary.encode message
  | .negotiationReject message => NegotiationReject.encode message
  | .negotiationResponse message => NegotiationResponse.encode message
  | .terminate message => Terminate.encode message
  | .requestAck message => RequestAck.encode message
  | .requestReject message => RequestReject.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 4 then (ChannelReset.decode bytes).map fun (message, rest) => (.channelReset message, rest)
  else if tag = 12 then (AdminHeartbeat.decode bytes).map fun (message, rest) => (.adminHeartbeat message, rest)
  else if tag = 15 then (AdminLogin.decode bytes).map fun (message, rest) => (.adminLogin message, rest)
  else if tag = 16 then (AdminLogout.decode bytes).map fun (message, rest) => (.adminLogout message, rest)
  else if tag = 27 then (MdInstrumentDefinitionFuture.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionFuture message, rest)
  else if tag = 29 then (MdInstrumentDefinitionSpread.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionSpread message, rest)
  else if tag = 30 then (SecurityStatus.decode bytes).map fun (message, rest) => (.securityStatus message, rest)
  else if tag = 32 then (MdIncrementalRefreshBook.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshBook message, rest)
  else if tag = 33 then (MdIncrementalRefreshDailyStatistics.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshDailyStatistics message, rest)
  else if tag = 34 then (MdIncrementalRefreshLimitsBanding.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshLimitsBanding message, rest)
  else if tag = 35 then (MdIncrementalRefreshSessionStatistics.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshSessionStatistics message, rest)
  else if tag = 36 then (MdIncrementalRefreshTrade.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshTrade message, rest)
  else if tag = 37 then (MdIncrementalRefreshVolume.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshVolume message, rest)
  else if tag = 38 then (SnapshotFullRefresh.decode bytes).map fun (message, rest) => (.snapshotFullRefresh message, rest)
  else if tag = 39 then (QuoteRequest.decode bytes).map fun (message, rest) => (.quoteRequest message, rest)
  else if tag = 41 then (MdInstrumentDefinitionOption.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionOption message, rest)
  else if tag = 42 then (MdIncrementalRefreshTradeSummary.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshTradeSummary message, rest)
  else if tag = 201 then (NegotiationReject.decode bytes).map fun (message, rest) => (.negotiationReject message, rest)
  else if tag = 202 then (NegotiationResponse.decode bytes).map fun (message, rest) => (.negotiationResponse message, rest)
  else if tag = 203 then (Terminate.decode bytes).map fun (message, rest) => (.terminate message, rest)
  else if tag = 206 then (RequestAck.decode bytes).map fun (message, rest) => (.requestAck message, rest)
  else if tag = 207 then (RequestReject.decode bytes).map fun (message, rest) => (.requestReject message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Tcp Message -/
structure ServerTcpMessage where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerTcpMessage

def encodeBody (message : ServerTcpMessage) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUIntLE 2 (ServerPayload.tag message.serverPayload)
    ++ encodeUIntLE 2 message.schemaId
    ++ encodeUIntLE 2 message.version
    ++ ServerPayload.encode message.serverPayload

def decodeBody (bytes : List UInt8) : Option (ServerTcpMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (serverPayload, bytes) ← ServerPayload.decode templateId bytes
  pure ({ blockLength, schemaId, version, serverPayload }, bytes)

theorem decodeBody_encodeBody (message : ServerTcpMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  simp [decodeBody, encodeBody, List.append_assoc]

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerTcpMessage) : (encodeBody message).length + 2 < 65536 := by
  cases h : message.serverPayload with
  | channelReset inner =>
    have bound_channelReset_channelResetGroup := inner.channelResetGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, ChannelReset.encode, encodeMany_length_const ChannelResetGroup.encode 2 ChannelResetGroup.encode_length]
    omega
  | adminHeartbeat inner =>
    simp [encodeBody, h, ServerPayload.encode, AdminHeartbeat.encode]
  | adminLogin inner =>
    simp [encodeBody, h, ServerPayload.encode, AdminLogin.encode]
  | adminLogout inner =>
    simp [encodeBody, h, ServerPayload.encode, AdminLogout.encode]
  | mdInstrumentDefinitionFuture inner =>
    have bound_mdInstrumentDefinitionFuture_eventsGroup := inner.eventsGroup.length_lt
    have bound_mdInstrumentDefinitionFuture_feedTypesGroup := inner.feedTypesGroup.length_lt
    have bound_mdInstrumentDefinitionFuture_instAttribGroup := inner.instAttribGroup.length_lt
    have bound_mdInstrumentDefinitionFuture_lotTypeRulesGroup := inner.lotTypeRulesGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdInstrumentDefinitionFuture.encode, encodeMany_length_const EventsGroup.encode 9 EventsGroup.encode_length, encodeMany_length_const FeedTypesGroup.encode 4 FeedTypesGroup.encode_length, encodeMany_length_const InstAttribGroup.encode 4 InstAttribGroup.encode_length, encodeMany_length_const LotTypeRulesGroup.encode 5 LotTypeRulesGroup.encode_length]
    omega
  | mdInstrumentDefinitionSpread inner =>
    have bound_mdInstrumentDefinitionSpread_eventsGroup := inner.eventsGroup.length_lt
    have bound_mdInstrumentDefinitionSpread_feedTypesGroup := inner.feedTypesGroup.length_lt
    have bound_mdInstrumentDefinitionSpread_instAttribGroup := inner.instAttribGroup.length_lt
    have bound_mdInstrumentDefinitionSpread_lotTypeRulesGroup := inner.lotTypeRulesGroup.length_lt
    have bound_mdInstrumentDefinitionSpread_legacyLegsGroup := inner.legacyLegsGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdInstrumentDefinitionSpread.encode, encodeMany_length_const EventsGroup.encode 9 EventsGroup.encode_length, encodeMany_length_const FeedTypesGroup.encode 4 FeedTypesGroup.encode_length, encodeMany_length_const InstAttribGroup.encode 4 InstAttribGroup.encode_length, encodeMany_length_const LotTypeRulesGroup.encode 5 LotTypeRulesGroup.encode_length, encodeMany_length_const LegacyLegsGroup.encode 18 LegacyLegsGroup.encode_length]
    omega
  | securityStatus inner =>
    simp [encodeBody, h, ServerPayload.encode, SecurityStatus.encode]
  | mdIncrementalRefreshBook inner =>
    have bound_mdIncrementalRefreshBook_incrementalRefreshBookGroup := inner.incrementalRefreshBookGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshBook.encode, encodeMany_length_const IncrementalRefreshBookGroup.encode 32 IncrementalRefreshBookGroup.encode_length]
    omega
  | mdIncrementalRefreshDailyStatistics inner =>
    have bound_mdIncrementalRefreshDailyStatistics_incrementalRefreshDailyStatisticsGroup := inner.incrementalRefreshDailyStatisticsGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshDailyStatistics.encode, encodeMany_length_const IncrementalRefreshDailyStatisticsGroup.encode 32 IncrementalRefreshDailyStatisticsGroup.encode_length]
    omega
  | mdIncrementalRefreshLimitsBanding inner =>
    have bound_mdIncrementalRefreshLimitsBanding_incrementalRefreshLimitsBandingGroup := inner.incrementalRefreshLimitsBandingGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshLimitsBanding.encode, encodeMany_length_const IncrementalRefreshLimitsBandingGroup.encode 32 IncrementalRefreshLimitsBandingGroup.encode_length]
    omega
  | mdIncrementalRefreshSessionStatistics inner =>
    have bound_mdIncrementalRefreshSessionStatistics_incrementalRefreshSessionStatisticsGroup := inner.incrementalRefreshSessionStatisticsGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshSessionStatistics.encode, encodeMany_length_const IncrementalRefreshSessionStatisticsGroup.encode 24 IncrementalRefreshSessionStatisticsGroup.encode_length]
    omega
  | mdIncrementalRefreshTrade inner =>
    have bound_mdIncrementalRefreshTrade_incrementalRefreshTradeGroup := inner.incrementalRefreshTradeGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshTrade.encode, encodeMany_length_const IncrementalRefreshTradeGroup.encode 32 IncrementalRefreshTradeGroup.encode_length]
    omega
  | mdIncrementalRefreshVolume inner =>
    have bound_mdIncrementalRefreshVolume_incrementalRefreshVolumeGroup := inner.incrementalRefreshVolumeGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshVolume.encode, encodeMany_length_const IncrementalRefreshVolumeGroup.encode 16 IncrementalRefreshVolumeGroup.encode_length]
    omega
  | snapshotFullRefresh inner =>
    have bound_snapshotFullRefresh_snapshotFullRefreshGroup := inner.snapshotFullRefreshGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, SnapshotFullRefresh.encode, encodeMany_length_const SnapshotFullRefreshGroup.encode 22 SnapshotFullRefreshGroup.encode_length]
    omega
  | quoteRequest inner =>
    have bound_quoteRequest_relatedSymGroup := inner.relatedSymGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, QuoteRequest.encode, encodeMany_length_const RelatedSymGroup.encode 32 RelatedSymGroup.encode_length]
    omega
  | mdInstrumentDefinitionOption inner =>
    have bound_mdInstrumentDefinitionOption_eventsGroup := inner.eventsGroup.length_lt
    have bound_mdInstrumentDefinitionOption_feedTypesGroup := inner.feedTypesGroup.length_lt
    have bound_mdInstrumentDefinitionOption_instAttribGroup := inner.instAttribGroup.length_lt
    have bound_mdInstrumentDefinitionOption_lotTypeRulesGroup := inner.lotTypeRulesGroup.length_lt
    have bound_mdInstrumentDefinitionOption_optionUnderlyingsGroup := inner.optionUnderlyingsGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdInstrumentDefinitionOption.encode, encodeMany_length_const EventsGroup.encode 9 EventsGroup.encode_length, encodeMany_length_const FeedTypesGroup.encode 4 FeedTypesGroup.encode_length, encodeMany_length_const InstAttribGroup.encode 4 InstAttribGroup.encode_length, encodeMany_length_const LotTypeRulesGroup.encode 5 LotTypeRulesGroup.encode_length, encodeMany_length_const OptionUnderlyingsGroup.encode 24 OptionUnderlyingsGroup.encode_length]
    omega
  | mdIncrementalRefreshTradeSummary inner =>
    have bound_mdIncrementalRefreshTradeSummary_incrementalRefreshTradeSummaryGroup := inner.incrementalRefreshTradeSummaryGroup.length_lt
    have bound_mdIncrementalRefreshTradeSummary_incrementalRefreshTradeSummaryOrderIdGroup := inner.incrementalRefreshTradeSummaryOrderIdGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshTradeSummary.encode, encodeMany_length_const IncrementalRefreshTradeSummaryGroup.encode 32 IncrementalRefreshTradeSummaryGroup.encode_length, encodeMany_length_const IncrementalRefreshTradeSummaryOrderIdGroup.encode 16 IncrementalRefreshTradeSummaryOrderIdGroup.encode_length]
    omega
  | negotiationReject inner =>
    simp [encodeBody, h, ServerPayload.encode, NegotiationReject.encode]
  | negotiationResponse inner =>
    simp [encodeBody, h, ServerPayload.encode, NegotiationResponse.encode]
  | terminate inner =>
    simp [encodeBody, h, ServerPayload.encode, Terminate.encode]
  | requestAck inner =>
    have bound_requestAck_requestAckSecurityGroup := inner.requestAckSecurityGroup.length_lt
    have bound_requestAck_requestAckRelatedSymbolGroup := inner.requestAckRelatedSymbolGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, RequestAck.encode, encodeMany_length_const RequestAckSecurityGroup.encode 6 RequestAckSecurityGroup.encode_length, encodeMany_length_const RequestAckRelatedSymbolGroup.encode 4 RequestAckRelatedSymbolGroup.encode_length]
    omega
  | requestReject inner =>
    simp [encodeBody, h, ServerPayload.encode, RequestReject.encode]

/-- Size rule: Tcp Message Size counts the bytes after it plus 2, so it is written from the body -/
def encode : ServerTcpMessage → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (ServerTcpMessage × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : ServerTcpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : ServerTcpMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end ServerTcpMessage

/-- Server Tcp Packet -/
structure ServerTcpPacket where
  serverTechnicalHeader : ServerTechnicalHeader
  serverTcpMessage : List ServerTcpMessage
  deriving DecidableEq, Repr

namespace ServerTcpPacket

def encode (message : ServerTcpPacket) : List UInt8 :=
  ServerTechnicalHeader.encode message.serverTechnicalHeader
    ++ encodeMany ServerTcpMessage.encode message.serverTcpMessage

def decode (bytes : List UInt8) : Option ServerTcpPacket := do
  let (serverTechnicalHeader, bytes) ← ServerTechnicalHeader.decode bytes
  let serverTcpMessage ← decodeAll ServerTcpMessage.decode bytes.length bytes
  pure { serverTechnicalHeader, serverTcpMessage }

theorem decode_encode (message : ServerTcpPacket) : decode (encode message) = some message := by
  simp [decode, encode, List.append_assoc, decodeAll_encodeMany ServerTcpMessage.encode ServerTcpMessage.decode ServerTcpMessage.decode_encode ServerTcpMessage.encode_length_pos message.serverTcpMessage _ (encodeMany_length_ge ServerTcpMessage.encode ServerTcpMessage.encode_length_pos message.serverTcpMessage)]

end ServerTcpPacket

end Omi.CmeGlobexMdp3SbeV15ServerTcp
