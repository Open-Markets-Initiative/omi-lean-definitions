import Omi.Wire

/-!
# CME Group Market Data Platform 3 v1.13

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

namespace Omi.CmeGlobexMdp3SbeV113ServerTcp

/-- Md Entry Type Book: one byte code -/
inductive MdEntryTypeBook where
  | bid -- Bid
  | offer -- Offer
  | impliedBid -- Implied Bid
  | impliedOffer -- Implied Offer
  | bookReset -- Book Reset
  | marketBestOffer -- Market Best Offer
  | marketBestBid -- Market Best Bid
  deriving DecidableEq, Repr

namespace MdEntryTypeBook

def toByte : MdEntryTypeBook → UInt8
  | .bid => 0x30
  | .offer => 0x31
  | .impliedBid => 0x45
  | .impliedOffer => 0x46
  | .bookReset => 0x4A
  | .marketBestOffer => 0x77
  | .marketBestBid => 0x78

def ofByte? (byte : UInt8) : Option MdEntryTypeBook :=
  if byte = 0x30 then some .bid
  else if byte = 0x31 then some .offer
  else if byte = 0x45 then some .impliedBid
  else if byte = 0x46 then some .impliedOffer
  else if byte = 0x4A then some .bookReset
  else if byte = 0x77 then some .marketBestOffer
  else if byte = 0x78 then some .marketBestBid
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
  | vwap -- Vwap
  | highestBid -- Highest Bid
  | lowestOffer -- Lowest Offer
  deriving DecidableEq, Repr

namespace MdEntryTypeStatistics

def toByte : MdEntryTypeStatistics → UInt8
  | .openPrice => 0x34
  | .highTrade => 0x37
  | .lowTrade => 0x38
  | .vwap => 0x39
  | .highestBid => 0x4E
  | .lowestOffer => 0x4F

def ofByte? (byte : UInt8) : Option MdEntryTypeStatistics :=
  if byte = 0x34 then some .openPrice
  else if byte = 0x37 then some .highTrade
  else if byte = 0x38 then some .lowTrade
  else if byte = 0x39 then some .vwap
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
  | openPrice -- Open Price
  | settlementPrice -- Settlement Price
  | tradingSessionHighPrice -- Trading Session High Price
  | tradingSessionLowPrice -- Trading Session Low Price
  | vwap -- Vwap
  | clearedVolume -- Cleared Volume
  | openInterest -- Open Interest
  | impliedBid -- Implied Bid
  | impliedOffer -- Implied Offer
  | bookReset -- Book Reset
  | sessionHighBid -- Session High Bid
  | sessionLowOffer -- Session Low Offer
  | fixingPrice -- Fixing Price
  | electronicVolume -- Electronic Volume
  | thresholdLimitsandPriceBandVariation -- Threshold Limitsand Price Band Variation
  | marketBestOffer -- Market Best Offer
  | marketBestBid -- Market Best Bid
  deriving DecidableEq, Repr

namespace MdEntryType

def toByte : MdEntryType → UInt8
  | .bid => 0x30
  | .offer => 0x31
  | .trade => 0x32
  | .openPrice => 0x34
  | .settlementPrice => 0x36
  | .tradingSessionHighPrice => 0x37
  | .tradingSessionLowPrice => 0x38
  | .vwap => 0x39
  | .clearedVolume => 0x42
  | .openInterest => 0x43
  | .impliedBid => 0x45
  | .impliedOffer => 0x46
  | .bookReset => 0x4A
  | .sessionHighBid => 0x4E
  | .sessionLowOffer => 0x4F
  | .fixingPrice => 0x57
  | .electronicVolume => 0x65
  | .thresholdLimitsandPriceBandVariation => 0x67
  | .marketBestOffer => 0x77
  | .marketBestBid => 0x78

def ofByte? (byte : UInt8) : Option MdEntryType :=
  if byte = 0x30 then some .bid
  else if byte = 0x31 then some .offer
  else if byte = 0x32 then some .trade
  else if byte = 0x34 then some .openPrice
  else if byte = 0x36 then some .settlementPrice
  else if byte = 0x37 then some .tradingSessionHighPrice
  else if byte = 0x38 then some .tradingSessionLowPrice
  else if byte = 0x39 then some .vwap
  else if byte = 0x42 then some .clearedVolume
  else if byte = 0x43 then some .openInterest
  else if byte = 0x45 then some .impliedBid
  else if byte = 0x46 then some .impliedOffer
  else if byte = 0x4A then some .bookReset
  else if byte = 0x4E then some .sessionHighBid
  else if byte = 0x4F then some .sessionLowOffer
  else if byte = 0x57 then some .fixingPrice
  else if byte = 0x65 then some .electronicVolume
  else if byte = 0x67 then some .thresholdLimitsandPriceBandVariation
  else if byte = 0x77 then some .marketBestOffer
  else if byte = 0x78 then some .marketBestBid
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

/-- Incremental Refresh Volume Group: 16 bytes -/
structure IncrementalRefreshVolumeGroup where
  mdEntrySizeShort : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  mdUpdateAction : BitVec 8
  padding3 : Alpha 3
  deriving DecidableEq, Repr

namespace IncrementalRefreshVolumeGroup

def encode (message : IncrementalRefreshVolumeGroup) : List UInt8 :=
  encodeUIntLE 4 message.mdEntrySizeShort
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUInt 1 message.mdUpdateAction
    ++ Alpha.encode message.padding3

def decode (bytes : List UInt8) : Option (IncrementalRefreshVolumeGroup × List UInt8) := do
  let (mdEntrySizeShort, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (padding3, bytes) ← Alpha.decode 3 bytes
  pure ({ mdEntrySizeShort, securityId, rptSeq, mdUpdateAction, padding3 }, bytes)

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

/-- Related Sym Group: 32 bytes -/
structure RelatedSymGroup where
  symbol : Alpha 20
  securityId : BitVec 32
  orderQty : BitVec 32
  quoteType : BitVec 8
  sideOptional : BitVec 8
  padding2 : Alpha 2
  deriving DecidableEq, Repr

namespace RelatedSymGroup

def encode (message : RelatedSymGroup) : List UInt8 :=
  Alpha.encode message.symbol
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUInt 1 message.quoteType
    ++ encodeUInt 1 message.sideOptional
    ++ Alpha.encode message.padding2

def decode (bytes : List UInt8) : Option (RelatedSymGroup × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (sideOptional, bytes) ← decodeUInt 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  pure ({ symbol, securityId, orderQty, quoteType, sideOptional, padding2 }, bytes)

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

/-- Incremental Refresh Book Group: 32 bytes -/
structure IncrementalRefreshBookGroup where
  mdEntryPxOptionalEx : BitVec 64
  mdEntrySizeShortOptional : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  numberOfOrdersOptional : BitVec 32
  mdPriceLevel : BitVec 8
  mdUpdateAction : BitVec 8
  mdEntryTypeBook : MdEntryTypeBook
  tradeableSize : BitVec 32
  padding1 : Alpha 1
  deriving DecidableEq, Repr

namespace IncrementalRefreshBookGroup

def encode (message : IncrementalRefreshBookGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxOptionalEx
    ++ encodeUIntLE 4 message.mdEntrySizeShortOptional
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 4 message.numberOfOrdersOptional
    ++ encodeUInt 1 message.mdPriceLevel
    ++ encodeUInt 1 message.mdUpdateAction
    ++ MdEntryTypeBook.encode message.mdEntryTypeBook
    ++ encodeUIntLE 4 message.tradeableSize
    ++ Alpha.encode message.padding1

def decode (bytes : List UInt8) : Option (IncrementalRefreshBookGroup × List UInt8) := do
  let (mdEntryPxOptionalEx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeShortOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrdersOptional, bytes) ← decodeUIntLE 4 bytes
  let (mdPriceLevel, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryTypeBook, bytes) ← MdEntryTypeBook.decode bytes
  let (tradeableSize, bytes) ← decodeUIntLE 4 bytes
  let (padding1, bytes) ← Alpha.decode 1 bytes
  pure ({ mdEntryPxOptionalEx, mdEntrySizeShortOptional, securityId, rptSeq, numberOfOrdersOptional, mdPriceLevel, mdUpdateAction, mdEntryTypeBook, tradeableSize, padding1 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshBookGroup) : (encode message).length = 32 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshBookGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshBookGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshBookGroup

/-- Incremental Refresh Book Order Id Group: 24 bytes -/
structure IncrementalRefreshBookOrderIdGroup where
  orderId : BitVec 64
  mdOrderPriorityOptional : BitVec 64
  mdDisplayQtyOptional : BitVec 32
  referenceId : BitVec 8
  orderUpdateAction : BitVec 8
  padding2 : Alpha 2
  deriving DecidableEq, Repr

namespace IncrementalRefreshBookOrderIdGroup

def encode (message : IncrementalRefreshBookOrderIdGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.mdOrderPriorityOptional
    ++ encodeUIntLE 4 message.mdDisplayQtyOptional
    ++ encodeUInt 1 message.referenceId
    ++ encodeUInt 1 message.orderUpdateAction
    ++ Alpha.encode message.padding2

def decode (bytes : List UInt8) : Option (IncrementalRefreshBookOrderIdGroup × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (mdOrderPriorityOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdDisplayQtyOptional, bytes) ← decodeUIntLE 4 bytes
  let (referenceId, bytes) ← decodeUInt 1 bytes
  let (orderUpdateAction, bytes) ← decodeUInt 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  pure ({ orderId, mdOrderPriorityOptional, mdDisplayQtyOptional, referenceId, orderUpdateAction, padding2 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshBookOrderIdGroup) : (encode message).length = 24 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshBookOrderIdGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshBookOrderIdGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshBookOrderIdGroup

/-- Md Incremental Refresh Book -/
structure MdIncrementalRefreshBook where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  incrementalRefreshBookGroup : Bounded 1 IncrementalRefreshBookGroup
  blockLength : BitVec 16
  padding5 : Alpha 5
  incrementalRefreshBookOrderIdGroup : Bounded 1 IncrementalRefreshBookOrderIdGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshBook

def encode (message : MdIncrementalRefreshBook) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshBookGroup.val.length)
    ++ encodeMany IncrementalRefreshBookGroup.encode message.incrementalRefreshBookGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ Alpha.encode message.padding5
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshBookOrderIdGroup.val.length)
    ++ encodeMany IncrementalRefreshBookOrderIdGroup.encode message.incrementalRefreshBookOrderIdGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshBook × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshBookGroup_, bytes) ← decodeMany IncrementalRefreshBookGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshBookOrderIdGroup_, bytes) ← decodeMany IncrementalRefreshBookOrderIdGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshBookGroup : incrementalRefreshBookGroup_.length < 256 then
    if fits_incrementalRefreshBookOrderIdGroup : incrementalRefreshBookOrderIdGroup_.length < 256 then
      pure ({ transactTime, matchEventIndicator, padding2, blockLength, incrementalRefreshBookGroup := ⟨incrementalRefreshBookGroup_, fits_incrementalRefreshBookGroup⟩, blockLength, padding5, incrementalRefreshBookOrderIdGroup := ⟨incrementalRefreshBookOrderIdGroup_, fits_incrementalRefreshBookOrderIdGroup⟩ }, bytes)
    else none
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshBook) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshBookGroup : message.incrementalRefreshBookGroup.val.length < 256 := by simpa using message.incrementalRefreshBookGroup.length_lt
  have fits_incrementalRefreshBookOrderIdGroup : message.incrementalRefreshBookOrderIdGroup.val.length < 256 := by simpa using message.incrementalRefreshBookOrderIdGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshBookGroup, fits_incrementalRefreshBookGroup, decodeMany_encodeMany IncrementalRefreshBookGroup.encode IncrementalRefreshBookGroup.decode IncrementalRefreshBookGroup.decode_encode, Nat.mod_eq_of_lt fits_incrementalRefreshBookOrderIdGroup, fits_incrementalRefreshBookOrderIdGroup, decodeMany_encodeMany IncrementalRefreshBookOrderIdGroup.encode IncrementalRefreshBookOrderIdGroup.decode IncrementalRefreshBookOrderIdGroup.decode_encode]

end MdIncrementalRefreshBook

/-- Incremental Refresh Order Book Group: 40 bytes -/
structure IncrementalRefreshOrderBookGroup where
  orderIdOptional : BitVec 64
  mdOrderPriorityOptional : BitVec 64
  mdEntryPxOptionalEx : BitVec 64
  mdDisplayQtyOptional : BitVec 32
  securityId : BitVec 32
  mdUpdateAction : BitVec 8
  mdEntryTypeBook : MdEntryTypeBook
  padding6 : Alpha 6
  deriving DecidableEq, Repr

namespace IncrementalRefreshOrderBookGroup

def encode (message : IncrementalRefreshOrderBookGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderIdOptional
    ++ encodeUIntLE 8 message.mdOrderPriorityOptional
    ++ encodeUIntLE 8 message.mdEntryPxOptionalEx
    ++ encodeUIntLE 4 message.mdDisplayQtyOptional
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUInt 1 message.mdUpdateAction
    ++ MdEntryTypeBook.encode message.mdEntryTypeBook
    ++ Alpha.encode message.padding6

def decode (bytes : List UInt8) : Option (IncrementalRefreshOrderBookGroup × List UInt8) := do
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdOrderPriorityOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryPxOptionalEx, bytes) ← decodeUIntLE 8 bytes
  let (mdDisplayQtyOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryTypeBook, bytes) ← MdEntryTypeBook.decode bytes
  let (padding6, bytes) ← Alpha.decode 6 bytes
  pure ({ orderIdOptional, mdOrderPriorityOptional, mdEntryPxOptionalEx, mdDisplayQtyOptional, securityId, mdUpdateAction, mdEntryTypeBook, padding6 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshOrderBookGroup) : (encode message).length = 40 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshOrderBookGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshOrderBookGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshOrderBookGroup

/-- Md Incremental Refresh Order Book -/
structure MdIncrementalRefreshOrderBook where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  incrementalRefreshOrderBookGroup : Bounded 1 IncrementalRefreshOrderBookGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshOrderBook

def encode (message : MdIncrementalRefreshOrderBook) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshOrderBookGroup.val.length)
    ++ encodeMany IncrementalRefreshOrderBookGroup.encode message.incrementalRefreshOrderBookGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshOrderBook × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshOrderBookGroup_, bytes) ← decodeMany IncrementalRefreshOrderBookGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshOrderBookGroup : incrementalRefreshOrderBookGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, padding2, blockLength, incrementalRefreshOrderBookGroup := ⟨incrementalRefreshOrderBookGroup_, fits_incrementalRefreshOrderBookGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshOrderBook) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshOrderBookGroup : message.incrementalRefreshOrderBookGroup.val.length < 256 := by simpa using message.incrementalRefreshOrderBookGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshOrderBookGroup, fits_incrementalRefreshOrderBookGroup, decodeMany_encodeMany IncrementalRefreshOrderBookGroup.encode IncrementalRefreshOrderBookGroup.decode IncrementalRefreshOrderBookGroup.decode_encode]

end MdIncrementalRefreshOrderBook

/-- Incremental Refresh Trade Summary Group: 32 bytes -/
structure IncrementalRefreshTradeSummaryGroup where
  mdEntryPxEx : BitVec 64
  mdEntrySizeShort : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  numberOfOrders : BitVec 32
  aggressorSide : BitVec 8
  mdUpdateAction : BitVec 8
  mdTradeEntryOptional : BitVec 32
  padding2 : Alpha 2
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeSummaryGroup

def encode (message : IncrementalRefreshTradeSummaryGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxEx
    ++ encodeUIntLE 4 message.mdEntrySizeShort
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 4 message.numberOfOrders
    ++ encodeUInt 1 message.aggressorSide
    ++ encodeUInt 1 message.mdUpdateAction
    ++ encodeUIntLE 4 message.mdTradeEntryOptional
    ++ Alpha.encode message.padding2

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeSummaryGroup × List UInt8) := do
  let (mdEntryPxEx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeShort, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdTradeEntryOptional, bytes) ← decodeUIntLE 4 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  pure ({ mdEntryPxEx, mdEntrySizeShort, securityId, rptSeq, numberOfOrders, aggressorSide, mdUpdateAction, mdTradeEntryOptional, padding2 }, bytes)

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

/-- Incremental Refresh Daily Statistics Group: 32 bytes -/
structure IncrementalRefreshDailyStatisticsGroup where
  mdEntryPxOptionalEx : BitVec 64
  mdEntrySizeShortOptional : BitVec 32
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
  encodeUIntLE 8 message.mdEntryPxOptionalEx
    ++ encodeUIntLE 4 message.mdEntrySizeShortOptional
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 2 message.tradingReferenceDate
    ++ encodeUIntLE 1 message.settlPriceType
    ++ encodeUInt 1 message.mdUpdateAction
    ++ MdEntryTypeDailyStatistics.encode message.mdEntryTypeDailyStatistics
    ++ Alpha.encode message.padding7

def decode (bytes : List UInt8) : Option (IncrementalRefreshDailyStatisticsGroup × List UInt8) := do
  let (mdEntryPxOptionalEx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeShortOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryTypeDailyStatistics, bytes) ← MdEntryTypeDailyStatistics.decode bytes
  let (padding7, bytes) ← Alpha.decode 7 bytes
  pure ({ mdEntryPxOptionalEx, mdEntrySizeShortOptional, securityId, rptSeq, tradingReferenceDate, settlPriceType, mdUpdateAction, mdEntryTypeDailyStatistics, padding7 }, bytes)

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
  mdEntryPxEx : BitVec 64
  securityId : BitVec 32
  rptSeq : BitVec 32
  openCloseSettlFlag : BitVec 8
  mdUpdateAction : BitVec 8
  mdEntryTypeStatistics : MdEntryTypeStatistics
  mdEntrySizeShortOptional : BitVec 32
  padding1 : Alpha 1
  deriving DecidableEq, Repr

namespace IncrementalRefreshSessionStatisticsGroup

def encode (message : IncrementalRefreshSessionStatisticsGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxEx
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ encodeUInt 1 message.mdUpdateAction
    ++ MdEntryTypeStatistics.encode message.mdEntryTypeStatistics
    ++ encodeUIntLE 4 message.mdEntrySizeShortOptional
    ++ Alpha.encode message.padding1

def decode (bytes : List UInt8) : Option (IncrementalRefreshSessionStatisticsGroup × List UInt8) := do
  let (mdEntryPxEx, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryTypeStatistics, bytes) ← MdEntryTypeStatistics.decode bytes
  let (mdEntrySizeShortOptional, bytes) ← decodeUIntLE 4 bytes
  let (padding1, bytes) ← Alpha.decode 1 bytes
  pure ({ mdEntryPxEx, securityId, rptSeq, openCloseSettlFlag, mdUpdateAction, mdEntryTypeStatistics, mdEntrySizeShortOptional, padding1 }, bytes)

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

/-- Snapshot Full Refresh Group: 22 bytes -/
structure SnapshotFullRefreshGroup where
  mdEntryPxOptionalEx : BitVec 64
  mdEntrySizeShortOptional : BitVec 32
  numberOfOrdersOptional : BitVec 32
  mdPriceLevelOptional : BitVec 8
  tradingReferenceDate : BitVec 16
  openCloseSettlFlag : BitVec 8
  settlPriceType : BitVec 8
  mdEntryType : MdEntryType
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshGroup

def encode (message : SnapshotFullRefreshGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxOptionalEx
    ++ encodeUIntLE 4 message.mdEntrySizeShortOptional
    ++ encodeUIntLE 4 message.numberOfOrdersOptional
    ++ encodeUInt 1 message.mdPriceLevelOptional
    ++ encodeUIntLE 2 message.tradingReferenceDate
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ encodeUIntLE 1 message.settlPriceType
    ++ MdEntryType.encode message.mdEntryType

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshGroup × List UInt8) := do
  let (mdEntryPxOptionalEx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeShortOptional, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrdersOptional, bytes) ← decodeUIntLE 4 bytes
  let (mdPriceLevelOptional, bytes) ← decodeUInt 1 bytes
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  pure ({ mdEntryPxOptionalEx, mdEntrySizeShortOptional, numberOfOrdersOptional, mdPriceLevelOptional, tradingReferenceDate, openCloseSettlFlag, settlPriceType, mdEntryType }, bytes)

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

/-- Snapshot Full Refresh Order Book Group: 29 bytes -/
structure SnapshotFullRefreshOrderBookGroup where
  orderId : BitVec 64
  mdOrderPriorityOptional : BitVec 64
  mdEntryPxEx : BitVec 64
  mdDisplayQty : BitVec 32
  mdEntryTypeBook : MdEntryTypeBook
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshOrderBookGroup

def encode (message : SnapshotFullRefreshOrderBookGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.mdOrderPriorityOptional
    ++ encodeUIntLE 8 message.mdEntryPxEx
    ++ encodeUIntLE 4 message.mdDisplayQty
    ++ MdEntryTypeBook.encode message.mdEntryTypeBook

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshOrderBookGroup × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (mdOrderPriorityOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryPxEx, bytes) ← decodeUIntLE 8 bytes
  let (mdDisplayQty, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryTypeBook, bytes) ← MdEntryTypeBook.decode bytes
  pure ({ orderId, mdOrderPriorityOptional, mdEntryPxEx, mdDisplayQty, mdEntryTypeBook }, bytes)

@[simp] theorem encode_length (message : SnapshotFullRefreshOrderBookGroup) : (encode message).length = 29 := by
  simp [encode]

theorem encode_length_pos (message : SnapshotFullRefreshOrderBookGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SnapshotFullRefreshOrderBookGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end SnapshotFullRefreshOrderBookGroup

/-- Snapshot Full Refresh Order Book -/
structure SnapshotFullRefreshOrderBook where
  lastMsgSeqNumProcessed : BitVec 32
  totNumReports : BitVec 32
  securityId : BitVec 32
  noChunks : BitVec 32
  currentChunk : BitVec 32
  transactTime : BitVec 64
  blockLength : BitVec 16
  snapshotFullRefreshOrderBookGroup : Bounded 1 SnapshotFullRefreshOrderBookGroup
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshOrderBook

def encode (message : SnapshotFullRefreshOrderBook) : List UInt8 :=
  encodeUIntLE 4 message.lastMsgSeqNumProcessed
    ++ encodeUIntLE 4 message.totNumReports
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.noChunks
    ++ encodeUIntLE 4 message.currentChunk
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.snapshotFullRefreshOrderBookGroup.val.length)
    ++ encodeMany SnapshotFullRefreshOrderBookGroup.encode message.snapshotFullRefreshOrderBookGroup.val

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshOrderBook × List UInt8) := do
  let (lastMsgSeqNumProcessed, bytes) ← decodeUIntLE 4 bytes
  let (totNumReports, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (noChunks, bytes) ← decodeUIntLE 4 bytes
  let (currentChunk, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotFullRefreshOrderBookGroup_, bytes) ← decodeMany SnapshotFullRefreshOrderBookGroup.decode numInGroup.toNat bytes
  if fits_snapshotFullRefreshOrderBookGroup : snapshotFullRefreshOrderBookGroup_.length < 256 then
    pure ({ lastMsgSeqNumProcessed, totNumReports, securityId, noChunks, currentChunk, transactTime, blockLength, snapshotFullRefreshOrderBookGroup := ⟨snapshotFullRefreshOrderBookGroup_, fits_snapshotFullRefreshOrderBookGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : SnapshotFullRefreshOrderBook) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_snapshotFullRefreshOrderBookGroup : message.snapshotFullRefreshOrderBookGroup.val.length < 256 := by simpa using message.snapshotFullRefreshOrderBookGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_snapshotFullRefreshOrderBookGroup, fits_snapshotFullRefreshOrderBookGroup, decodeMany_encodeMany SnapshotFullRefreshOrderBookGroup.encode SnapshotFullRefreshOrderBookGroup.decode SnapshotFullRefreshOrderBookGroup.decode_encode]

end SnapshotFullRefreshOrderBook

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
  minLotSizeDecimalQty : BitVec 32
  deriving DecidableEq, Repr

namespace LotTypeRulesGroup

def encode (message : LotTypeRulesGroup) : List UInt8 :=
  encodeUInt 1 message.lotType
    ++ encodeUIntLE 4 message.minLotSizeDecimalQty

def decode (bytes : List UInt8) : Option (LotTypeRulesGroup × List UInt8) := do
  let (lotType, bytes) ← decodeUInt 1 bytes
  let (minLotSizeDecimalQty, bytes) ← decodeUIntLE 4 bytes
  pure ({ lotType, minLotSizeDecimalQty }, bytes)

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
  minPriceIncrementEx : BitVec 64
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
  tradingReferenceDate : BitVec 16
  instrumentGuid : BitVec 64
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
    ++ encodeUIntLE 8 message.minPriceIncrementEx
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
    ++ encodeUIntLE 2 message.tradingReferenceDate
    ++ encodeUIntLE 8 message.instrumentGuid
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
  let (minPriceIncrementEx, bytes) ← decodeUIntLE 8 bytes
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
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
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
          pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, maturityMonthYear, currency, settlCurrency, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementEx, displayFactor, mainFraction, subFraction, priceDisplayFormat, unitOfMeasure, unitOfMeasureQty, tradingReferencePrice, settlPriceType, openInterestQty, clearedVolume, highLimitPrice, lowLimitPrice, maxPriceVariation, decayQuantity, decayStartDate, originalContractSize, contractMultiplier, contractMultiplierUnit, flowScheduleType, minPriceIncrementAmount, userDefinedInstrument, tradingReferenceDate, instrumentGuid, blockLength, eventsGroup := ⟨eventsGroup_, fits_eventsGroup⟩, blockLength, feedTypesGroup := ⟨feedTypesGroup_, fits_feedTypesGroup⟩, blockLength, instAttribGroup := ⟨instAttribGroup_, fits_instAttribGroup⟩, blockLength, lotTypeRulesGroup := ⟨lotTypeRulesGroup_, fits_lotTypeRulesGroup⟩ }, bytes)
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

/-- Option Related Instruments Group: 24 bytes -/
structure OptionRelatedInstrumentsGroup where
  relatedSecurityId : BitVec 32
  relatedSymbol : Alpha 20
  deriving DecidableEq, Repr

namespace OptionRelatedInstrumentsGroup

def encode (message : OptionRelatedInstrumentsGroup) : List UInt8 :=
  encodeUIntLE 4 message.relatedSecurityId
    ++ Alpha.encode message.relatedSymbol

def decode (bytes : List UInt8) : Option (OptionRelatedInstrumentsGroup × List UInt8) := do
  let (relatedSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (relatedSymbol, bytes) ← Alpha.decode 20 bytes
  pure ({ relatedSecurityId, relatedSymbol }, bytes)

@[simp] theorem encode_length (message : OptionRelatedInstrumentsGroup) : (encode message).length = 24 := by
  simp [encode]

theorem encode_length_pos (message : OptionRelatedInstrumentsGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : OptionRelatedInstrumentsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end OptionRelatedInstrumentsGroup

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
  minPriceIncrementOptionalEx : BitVec 64
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
  tradingReferenceDate : BitVec 16
  instrumentGuid : BitVec 64
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
  blockLength : BitVec 16
  optionRelatedInstrumentsGroup : Bounded 1 OptionRelatedInstrumentsGroup
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
    ++ encodeUIntLE 8 message.minPriceIncrementOptionalEx
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
    ++ encodeUIntLE 2 message.tradingReferenceDate
    ++ encodeUIntLE 8 message.instrumentGuid
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
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.optionRelatedInstrumentsGroup.val.length)
    ++ encodeMany OptionRelatedInstrumentsGroup.encode message.optionRelatedInstrumentsGroup.val

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
  let (minPriceIncrementOptionalEx, bytes) ← decodeUIntLE 8 bytes
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
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
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
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (optionRelatedInstrumentsGroup_, bytes) ← decodeMany OptionRelatedInstrumentsGroup.decode numInGroup.toNat bytes
  if fits_eventsGroup : eventsGroup_.length < 256 then
    if fits_feedTypesGroup : feedTypesGroup_.length < 256 then
      if fits_instAttribGroup : instAttribGroup_.length < 256 then
        if fits_lotTypeRulesGroup : lotTypeRulesGroup_.length < 256 then
          if fits_optionUnderlyingsGroup : optionUnderlyingsGroup_.length < 256 then
            if fits_optionRelatedInstrumentsGroup : optionRelatedInstrumentsGroup_.length < 256 then
              pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, putOrCall, maturityMonthYear, currency, strikePrice, strikeCurrency, settlCurrency, minCabPrice, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementOptionalEx, minPriceIncrementAmount, displayFactor, tickRule, mainFraction, subFraction, priceDisplayFormat, unitOfMeasure, unitOfMeasureQty, tradingReferencePrice, settlPriceType, clearedVolume, openInterestQty, lowLimitPrice, highLimitPrice, userDefinedInstrument, tradingReferenceDate, instrumentGuid, blockLength, eventsGroup := ⟨eventsGroup_, fits_eventsGroup⟩, blockLength, feedTypesGroup := ⟨feedTypesGroup_, fits_feedTypesGroup⟩, blockLength, instAttribGroup := ⟨instAttribGroup_, fits_instAttribGroup⟩, blockLength, lotTypeRulesGroup := ⟨lotTypeRulesGroup_, fits_lotTypeRulesGroup⟩, blockLength, optionUnderlyingsGroup := ⟨optionUnderlyingsGroup_, fits_optionUnderlyingsGroup⟩, blockLength, optionRelatedInstrumentsGroup := ⟨optionRelatedInstrumentsGroup_, fits_optionRelatedInstrumentsGroup⟩ }, bytes)
            else none
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
  have fits_optionRelatedInstrumentsGroup : message.optionRelatedInstrumentsGroup.val.length < 256 := by simpa using message.optionRelatedInstrumentsGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_eventsGroup, fits_eventsGroup, decodeMany_encodeMany EventsGroup.encode EventsGroup.decode EventsGroup.decode_encode, Nat.mod_eq_of_lt fits_feedTypesGroup, fits_feedTypesGroup, decodeMany_encodeMany FeedTypesGroup.encode FeedTypesGroup.decode FeedTypesGroup.decode_encode, Nat.mod_eq_of_lt fits_instAttribGroup, fits_instAttribGroup, decodeMany_encodeMany InstAttribGroup.encode InstAttribGroup.decode InstAttribGroup.decode_encode, Nat.mod_eq_of_lt fits_lotTypeRulesGroup, fits_lotTypeRulesGroup, decodeMany_encodeMany LotTypeRulesGroup.encode LotTypeRulesGroup.decode LotTypeRulesGroup.decode_encode, Nat.mod_eq_of_lt fits_optionUnderlyingsGroup, fits_optionUnderlyingsGroup, decodeMany_encodeMany OptionUnderlyingsGroup.encode OptionUnderlyingsGroup.decode OptionUnderlyingsGroup.decode_encode, Nat.mod_eq_of_lt fits_optionRelatedInstrumentsGroup, fits_optionRelatedInstrumentsGroup, decodeMany_encodeMany OptionRelatedInstrumentsGroup.encode OptionRelatedInstrumentsGroup.decode OptionRelatedInstrumentsGroup.decode_encode]

end MdInstrumentDefinitionOption

/-- Legs Group: 18 bytes -/
structure LegsGroup where
  legSecurityId : BitVec 32
  legSide : BitVec 8
  legRatioQty : BitVec 8
  legPrice : BitVec 64
  legOptionDelta : BitVec 32
  deriving DecidableEq, Repr

namespace LegsGroup

def encode (message : LegsGroup) : List UInt8 :=
  encodeUIntLE 4 message.legSecurityId
    ++ encodeUInt 1 message.legSide
    ++ encodeUInt 1 message.legRatioQty
    ++ encodeUIntLE 8 message.legPrice
    ++ encodeUIntLE 4 message.legOptionDelta

def decode (bytes : List UInt8) : Option (LegsGroup × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (legRatioQty, bytes) ← decodeUInt 1 bytes
  let (legPrice, bytes) ← decodeUIntLE 8 bytes
  let (legOptionDelta, bytes) ← decodeUIntLE 4 bytes
  pure ({ legSecurityId, legSide, legRatioQty, legPrice, legOptionDelta }, bytes)

@[simp] theorem encode_length (message : LegsGroup) : (encode message).length = 18 := by
  simp [encode]

theorem encode_length_pos (message : LegsGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end LegsGroup

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
  minPriceIncrementOptionalEx : BitVec 64
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
  tradingReferenceDate : BitVec 16
  priceQuoteMethod : Alpha 5
  riskSet : Alpha 6
  marketSet : Alpha 6
  instrumentGuid : BitVec 64
  financialInstrumentFullName : Alpha 35
  blockLength : BitVec 16
  eventsGroup : Bounded 1 EventsGroup
  blockLength : BitVec 16
  feedTypesGroup : Bounded 1 FeedTypesGroup
  blockLength : BitVec 16
  instAttribGroup : Bounded 1 InstAttribGroup
  blockLength : BitVec 16
  lotTypeRulesGroup : Bounded 1 LotTypeRulesGroup
  blockLength : BitVec 16
  legsGroup : Bounded 1 LegsGroup
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
    ++ encodeUIntLE 8 message.minPriceIncrementOptionalEx
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
    ++ encodeUIntLE 2 message.tradingReferenceDate
    ++ Alpha.encode message.priceQuoteMethod
    ++ Alpha.encode message.riskSet
    ++ Alpha.encode message.marketSet
    ++ encodeUIntLE 8 message.instrumentGuid
    ++ Alpha.encode message.financialInstrumentFullName
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
    ++ encodeUInt 1 (BitVec.ofNat 8 message.legsGroup.val.length)
    ++ encodeMany LegsGroup.encode message.legsGroup.val

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
  let (minPriceIncrementOptionalEx, bytes) ← decodeUIntLE 8 bytes
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
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (priceQuoteMethod, bytes) ← Alpha.decode 5 bytes
  let (riskSet, bytes) ← Alpha.decode 6 bytes
  let (marketSet, bytes) ← Alpha.decode 6 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
  let (financialInstrumentFullName, bytes) ← Alpha.decode 35 bytes
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
  let (legsGroup_, bytes) ← decodeMany LegsGroup.decode numInGroup.toNat bytes
  if fits_eventsGroup : eventsGroup_.length < 256 then
    if fits_feedTypesGroup : feedTypesGroup_.length < 256 then
      if fits_instAttribGroup : instAttribGroup_.length < 256 then
        if fits_lotTypeRulesGroup : lotTypeRulesGroup_.length < 256 then
          if fits_legsGroup : legsGroup_.length < 256 then
            pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProductOptional, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, maturityMonthYear, currency, securitySubType, userDefinedInstrument, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementOptionalEx, displayFactor, priceDisplayFormat, priceRatio, tickRule, unitOfMeasure, tradingReferencePrice, settlPriceType, openInterestQty, clearedVolume, highLimitPrice, lowLimitPrice, maxPriceVariation, mainFraction, subFraction, tradingReferenceDate, priceQuoteMethod, riskSet, marketSet, instrumentGuid, financialInstrumentFullName, blockLength, eventsGroup := ⟨eventsGroup_, fits_eventsGroup⟩, blockLength, feedTypesGroup := ⟨feedTypesGroup_, fits_feedTypesGroup⟩, blockLength, instAttribGroup := ⟨instAttribGroup_, fits_instAttribGroup⟩, blockLength, lotTypeRulesGroup := ⟨lotTypeRulesGroup_, fits_lotTypeRulesGroup⟩, blockLength, legsGroup := ⟨legsGroup_, fits_legsGroup⟩ }, bytes)
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
  have fits_legsGroup : message.legsGroup.val.length < 256 := by simpa using message.legsGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_eventsGroup, fits_eventsGroup, decodeMany_encodeMany EventsGroup.encode EventsGroup.decode EventsGroup.decode_encode, Nat.mod_eq_of_lt fits_feedTypesGroup, fits_feedTypesGroup, decodeMany_encodeMany FeedTypesGroup.encode FeedTypesGroup.decode FeedTypesGroup.decode_encode, Nat.mod_eq_of_lt fits_instAttribGroup, fits_instAttribGroup, decodeMany_encodeMany InstAttribGroup.encode InstAttribGroup.decode InstAttribGroup.decode_encode, Nat.mod_eq_of_lt fits_lotTypeRulesGroup, fits_lotTypeRulesGroup, decodeMany_encodeMany LotTypeRulesGroup.encode LotTypeRulesGroup.decode LotTypeRulesGroup.decode_encode, Nat.mod_eq_of_lt fits_legsGroup, fits_legsGroup, decodeMany_encodeMany LegsGroup.encode LegsGroup.decode LegsGroup.decode_encode]

end MdInstrumentDefinitionSpread

/-- Md Instrument Definition Fixed Income -/
structure MdInstrumentDefinitionFixedIncome where
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
  currency : Alpha 3
  settlCurrency : Alpha 3
  matchAlgorithm : Alpha 1
  minTradeVol : BitVec 32
  maxTradeVol : BitVec 32
  minPriceIncrementOptionalEx : BitVec 64
  displayFactor : BitVec 64
  mainFraction : BitVec 8
  subFraction : BitVec 8
  priceDisplayFormat : BitVec 8
  unitOfMeasure : Alpha 30
  unitOfMeasureQty : BitVec 64
  tradingReferencePrice : BitVec 64
  tradingReferenceDate : BitVec 16
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  minPriceIncrementAmount : BitVec 64
  issueDate : BitVec 16
  datedDate : BitVec 16
  maturityDate : BitVec 16
  couponRate : BitVec 64
  parValue : BitVec 64
  couponFrequencyUnit : Alpha 3
  couponFrequencyPeriod : BitVec 16
  couponDayCount : Alpha 20
  countryOfIssue : Alpha 2
  issuer : Alpha 25
  financialInstrumentFullName : Alpha 35
  securityAltId : Alpha 12
  securityAltIdSource : BitVec 8
  priceQuoteMethod : Alpha 5
  partyRoleClearingOrg : Alpha 5
  userDefinedInstrument : Alpha 1
  riskSet : Alpha 6
  marketSet : Alpha 6
  instrumentGuid : BitVec 64
  blockLength : BitVec 16
  eventsGroup : Bounded 1 EventsGroup
  blockLength : BitVec 16
  feedTypesGroup : Bounded 1 FeedTypesGroup
  blockLength : BitVec 16
  instAttribGroup : Bounded 1 InstAttribGroup
  blockLength : BitVec 16
  lotTypeRulesGroup : Bounded 1 LotTypeRulesGroup
  deriving DecidableEq, Repr

namespace MdInstrumentDefinitionFixedIncome

def encode (message : MdInstrumentDefinitionFixedIncome) : List UInt8 :=
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
    ++ Alpha.encode message.currency
    ++ Alpha.encode message.settlCurrency
    ++ Alpha.encode message.matchAlgorithm
    ++ encodeUIntLE 4 message.minTradeVol
    ++ encodeUIntLE 4 message.maxTradeVol
    ++ encodeUIntLE 8 message.minPriceIncrementOptionalEx
    ++ encodeUIntLE 8 message.displayFactor
    ++ encodeUInt 1 message.mainFraction
    ++ encodeUInt 1 message.subFraction
    ++ encodeUInt 1 message.priceDisplayFormat
    ++ Alpha.encode message.unitOfMeasure
    ++ encodeUIntLE 8 message.unitOfMeasureQty
    ++ encodeUIntLE 8 message.tradingReferencePrice
    ++ encodeUIntLE 2 message.tradingReferenceDate
    ++ encodeUIntLE 8 message.highLimitPrice
    ++ encodeUIntLE 8 message.lowLimitPrice
    ++ encodeUIntLE 8 message.maxPriceVariation
    ++ encodeUIntLE 8 message.minPriceIncrementAmount
    ++ encodeUIntLE 2 message.issueDate
    ++ encodeUIntLE 2 message.datedDate
    ++ encodeUIntLE 2 message.maturityDate
    ++ encodeUIntLE 8 message.couponRate
    ++ encodeUIntLE 8 message.parValue
    ++ Alpha.encode message.couponFrequencyUnit
    ++ encodeUIntLE 2 message.couponFrequencyPeriod
    ++ Alpha.encode message.couponDayCount
    ++ Alpha.encode message.countryOfIssue
    ++ Alpha.encode message.issuer
    ++ Alpha.encode message.financialInstrumentFullName
    ++ Alpha.encode message.securityAltId
    ++ encodeUInt 1 message.securityAltIdSource
    ++ Alpha.encode message.priceQuoteMethod
    ++ Alpha.encode message.partyRoleClearingOrg
    ++ Alpha.encode message.userDefinedInstrument
    ++ Alpha.encode message.riskSet
    ++ Alpha.encode message.marketSet
    ++ encodeUIntLE 8 message.instrumentGuid
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

def decode (bytes : List UInt8) : Option (MdInstrumentDefinitionFixedIncome × List UInt8) := do
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
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (settlCurrency, bytes) ← Alpha.decode 3 bytes
  let (matchAlgorithm, bytes) ← Alpha.decode 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (maxTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (minPriceIncrementOptionalEx, bytes) ← decodeUIntLE 8 bytes
  let (displayFactor, bytes) ← decodeUIntLE 8 bytes
  let (mainFraction, bytes) ← decodeUInt 1 bytes
  let (subFraction, bytes) ← decodeUInt 1 bytes
  let (priceDisplayFormat, bytes) ← decodeUInt 1 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 30 bytes
  let (unitOfMeasureQty, bytes) ← decodeUIntLE 8 bytes
  let (tradingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (minPriceIncrementAmount, bytes) ← decodeUIntLE 8 bytes
  let (issueDate, bytes) ← decodeUIntLE 2 bytes
  let (datedDate, bytes) ← decodeUIntLE 2 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (couponRate, bytes) ← decodeUIntLE 8 bytes
  let (parValue, bytes) ← decodeUIntLE 8 bytes
  let (couponFrequencyUnit, bytes) ← Alpha.decode 3 bytes
  let (couponFrequencyPeriod, bytes) ← decodeUIntLE 2 bytes
  let (couponDayCount, bytes) ← Alpha.decode 20 bytes
  let (countryOfIssue, bytes) ← Alpha.decode 2 bytes
  let (issuer, bytes) ← Alpha.decode 25 bytes
  let (financialInstrumentFullName, bytes) ← Alpha.decode 35 bytes
  let (securityAltId, bytes) ← Alpha.decode 12 bytes
  let (securityAltIdSource, bytes) ← decodeUInt 1 bytes
  let (priceQuoteMethod, bytes) ← Alpha.decode 5 bytes
  let (partyRoleClearingOrg, bytes) ← Alpha.decode 5 bytes
  let (userDefinedInstrument, bytes) ← Alpha.decode 1 bytes
  let (riskSet, bytes) ← Alpha.decode 6 bytes
  let (marketSet, bytes) ← Alpha.decode 6 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
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
          pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, currency, settlCurrency, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementOptionalEx, displayFactor, mainFraction, subFraction, priceDisplayFormat, unitOfMeasure, unitOfMeasureQty, tradingReferencePrice, tradingReferenceDate, highLimitPrice, lowLimitPrice, maxPriceVariation, minPriceIncrementAmount, issueDate, datedDate, maturityDate, couponRate, parValue, couponFrequencyUnit, couponFrequencyPeriod, couponDayCount, countryOfIssue, issuer, financialInstrumentFullName, securityAltId, securityAltIdSource, priceQuoteMethod, partyRoleClearingOrg, userDefinedInstrument, riskSet, marketSet, instrumentGuid, blockLength, eventsGroup := ⟨eventsGroup_, fits_eventsGroup⟩, blockLength, feedTypesGroup := ⟨feedTypesGroup_, fits_feedTypesGroup⟩, blockLength, instAttribGroup := ⟨instAttribGroup_, fits_instAttribGroup⟩, blockLength, lotTypeRulesGroup := ⟨lotTypeRulesGroup_, fits_lotTypeRulesGroup⟩ }, bytes)
        else none
      else none
    else none
  else none

@[simp] theorem decode_encode (message : MdInstrumentDefinitionFixedIncome) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_eventsGroup : message.eventsGroup.val.length < 256 := by simpa using message.eventsGroup.length_lt
  have fits_feedTypesGroup : message.feedTypesGroup.val.length < 256 := by simpa using message.feedTypesGroup.length_lt
  have fits_instAttribGroup : message.instAttribGroup.val.length < 256 := by simpa using message.instAttribGroup.length_lt
  have fits_lotTypeRulesGroup : message.lotTypeRulesGroup.val.length < 256 := by simpa using message.lotTypeRulesGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_eventsGroup, fits_eventsGroup, decodeMany_encodeMany EventsGroup.encode EventsGroup.decode EventsGroup.decode_encode, Nat.mod_eq_of_lt fits_feedTypesGroup, fits_feedTypesGroup, decodeMany_encodeMany FeedTypesGroup.encode FeedTypesGroup.decode FeedTypesGroup.decode_encode, Nat.mod_eq_of_lt fits_instAttribGroup, fits_instAttribGroup, decodeMany_encodeMany InstAttribGroup.encode InstAttribGroup.decode InstAttribGroup.decode_encode, Nat.mod_eq_of_lt fits_lotTypeRulesGroup, fits_lotTypeRulesGroup, decodeMany_encodeMany LotTypeRulesGroup.encode LotTypeRulesGroup.decode LotTypeRulesGroup.decode_encode]

end MdInstrumentDefinitionFixedIncome

/-- Repo Underlyings Group: 118 bytes -/
structure RepoUnderlyingsGroup where
  underlyingSymbol : Alpha 20
  underlyingSecurityIdOptional : BitVec 32
  underlyingSecurityAltId : Alpha 12
  underlyingSecurityAltIdSource : BitVec 8
  underlyingFinancialInstrumentFullName : Alpha 35
  underlyingSecurityType : Alpha 6
  underlyingCountryOfIssue : Alpha 2
  underlyingIssuer : Alpha 25
  underlyingMaxLifeTime : BitVec 8
  underlyingMinDaysToMaturity : BitVec 16
  underlyingInstrumentGuidOptional : BitVec 64
  underlyingMaturityDate : BitVec 16
  deriving DecidableEq, Repr

namespace RepoUnderlyingsGroup

def encode (message : RepoUnderlyingsGroup) : List UInt8 :=
  Alpha.encode message.underlyingSymbol
    ++ encodeUIntLE 4 message.underlyingSecurityIdOptional
    ++ Alpha.encode message.underlyingSecurityAltId
    ++ encodeUInt 1 message.underlyingSecurityAltIdSource
    ++ Alpha.encode message.underlyingFinancialInstrumentFullName
    ++ Alpha.encode message.underlyingSecurityType
    ++ Alpha.encode message.underlyingCountryOfIssue
    ++ Alpha.encode message.underlyingIssuer
    ++ encodeUInt 1 message.underlyingMaxLifeTime
    ++ encodeUIntLE 2 message.underlyingMinDaysToMaturity
    ++ encodeUIntLE 8 message.underlyingInstrumentGuidOptional
    ++ encodeUIntLE 2 message.underlyingMaturityDate

def decode (bytes : List UInt8) : Option (RepoUnderlyingsGroup × List UInt8) := do
  let (underlyingSymbol, bytes) ← Alpha.decode 20 bytes
  let (underlyingSecurityIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSecurityAltId, bytes) ← Alpha.decode 12 bytes
  let (underlyingSecurityAltIdSource, bytes) ← decodeUInt 1 bytes
  let (underlyingFinancialInstrumentFullName, bytes) ← Alpha.decode 35 bytes
  let (underlyingSecurityType, bytes) ← Alpha.decode 6 bytes
  let (underlyingCountryOfIssue, bytes) ← Alpha.decode 2 bytes
  let (underlyingIssuer, bytes) ← Alpha.decode 25 bytes
  let (underlyingMaxLifeTime, bytes) ← decodeUInt 1 bytes
  let (underlyingMinDaysToMaturity, bytes) ← decodeUIntLE 2 bytes
  let (underlyingInstrumentGuidOptional, bytes) ← decodeUIntLE 8 bytes
  let (underlyingMaturityDate, bytes) ← decodeUIntLE 2 bytes
  pure ({ underlyingSymbol, underlyingSecurityIdOptional, underlyingSecurityAltId, underlyingSecurityAltIdSource, underlyingFinancialInstrumentFullName, underlyingSecurityType, underlyingCountryOfIssue, underlyingIssuer, underlyingMaxLifeTime, underlyingMinDaysToMaturity, underlyingInstrumentGuidOptional, underlyingMaturityDate }, bytes)

@[simp] theorem encode_length (message : RepoUnderlyingsGroup) : (encode message).length = 118 := by
  simp [encode]

theorem encode_length_pos (message : RepoUnderlyingsGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : RepoUnderlyingsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end RepoUnderlyingsGroup

/-- Repo Related Instruments Group: 32 bytes -/
structure RepoRelatedInstrumentsGroup where
  relatedSecurityId : BitVec 32
  relatedSymbol : Alpha 20
  relatedInstrumentGuid : BitVec 64
  deriving DecidableEq, Repr

namespace RepoRelatedInstrumentsGroup

def encode (message : RepoRelatedInstrumentsGroup) : List UInt8 :=
  encodeUIntLE 4 message.relatedSecurityId
    ++ Alpha.encode message.relatedSymbol
    ++ encodeUIntLE 8 message.relatedInstrumentGuid

def decode (bytes : List UInt8) : Option (RepoRelatedInstrumentsGroup × List UInt8) := do
  let (relatedSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (relatedSymbol, bytes) ← Alpha.decode 20 bytes
  let (relatedInstrumentGuid, bytes) ← decodeUIntLE 8 bytes
  pure ({ relatedSecurityId, relatedSymbol, relatedInstrumentGuid }, bytes)

@[simp] theorem encode_length (message : RepoRelatedInstrumentsGroup) : (encode message).length = 32 := by
  simp [encode]

theorem encode_length_pos (message : RepoRelatedInstrumentsGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : RepoRelatedInstrumentsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end RepoRelatedInstrumentsGroup

/-- Broken Dates Group: 16 bytes -/
structure BrokenDatesGroup where
  brokenDateGuid : BitVec 64
  brokenDateSecurityId : BitVec 32
  brokenDateStart : BitVec 16
  brokenDateEnd : BitVec 16
  deriving DecidableEq, Repr

namespace BrokenDatesGroup

def encode (message : BrokenDatesGroup) : List UInt8 :=
  encodeUIntLE 8 message.brokenDateGuid
    ++ encodeUIntLE 4 message.brokenDateSecurityId
    ++ encodeUIntLE 2 message.brokenDateStart
    ++ encodeUIntLE 2 message.brokenDateEnd

def decode (bytes : List UInt8) : Option (BrokenDatesGroup × List UInt8) := do
  let (brokenDateGuid, bytes) ← decodeUIntLE 8 bytes
  let (brokenDateSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (brokenDateStart, bytes) ← decodeUIntLE 2 bytes
  let (brokenDateEnd, bytes) ← decodeUIntLE 2 bytes
  pure ({ brokenDateGuid, brokenDateSecurityId, brokenDateStart, brokenDateEnd }, bytes)

@[simp] theorem encode_length (message : BrokenDatesGroup) : (encode message).length = 16 := by
  simp [encode]

theorem encode_length_pos (message : BrokenDatesGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : BrokenDatesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end BrokenDatesGroup

/-- Md Instrument Definition Repo -/
structure MdInstrumentDefinitionRepo where
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
  currency : Alpha 3
  settlCurrency : Alpha 3
  matchAlgorithm : Alpha 1
  minTradeVol : BitVec 32
  maxTradeVol : BitVec 32
  minPriceIncrementEx : BitVec 64
  displayFactor : BitVec 64
  unitOfMeasure : Alpha 30
  unitOfMeasureQty : BitVec 64
  tradingReferencePrice : BitVec 64
  tradingReferenceDate : BitVec 16
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  financialInstrumentFullName : Alpha 35
  partyRoleClearingOrg : Alpha 5
  startDate : BitVec 16
  endDate : BitVec 16
  terminationType : Alpha 8
  repoSubType : BitVec 8
  moneyOrPar : BitVec 8
  maxNoOfSubstitutions : BitVec 8
  priceQuoteMethod : Alpha 5
  userDefinedInstrument : Alpha 1
  riskSet : Alpha 6
  marketSet : Alpha 6
  instrumentGuid : BitVec 64
  termCode : Alpha 20
  brokenDateTermType : BitVec 8
  blockLength : BitVec 16
  eventsGroup : Bounded 1 EventsGroup
  blockLength : BitVec 16
  feedTypesGroup : Bounded 1 FeedTypesGroup
  blockLength : BitVec 16
  instAttribGroup : Bounded 1 InstAttribGroup
  blockLength : BitVec 16
  lotTypeRulesGroup : Bounded 1 LotTypeRulesGroup
  blockLength : BitVec 16
  repoUnderlyingsGroup : Bounded 1 RepoUnderlyingsGroup
  blockLength : BitVec 16
  repoRelatedInstrumentsGroup : Bounded 1 RepoRelatedInstrumentsGroup
  blockLength : BitVec 16
  brokenDatesGroup : Bounded 1 BrokenDatesGroup
  deriving DecidableEq, Repr

namespace MdInstrumentDefinitionRepo

def encode (message : MdInstrumentDefinitionRepo) : List UInt8 :=
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
    ++ Alpha.encode message.currency
    ++ Alpha.encode message.settlCurrency
    ++ Alpha.encode message.matchAlgorithm
    ++ encodeUIntLE 4 message.minTradeVol
    ++ encodeUIntLE 4 message.maxTradeVol
    ++ encodeUIntLE 8 message.minPriceIncrementEx
    ++ encodeUIntLE 8 message.displayFactor
    ++ Alpha.encode message.unitOfMeasure
    ++ encodeUIntLE 8 message.unitOfMeasureQty
    ++ encodeUIntLE 8 message.tradingReferencePrice
    ++ encodeUIntLE 2 message.tradingReferenceDate
    ++ encodeUIntLE 8 message.highLimitPrice
    ++ encodeUIntLE 8 message.lowLimitPrice
    ++ encodeUIntLE 8 message.maxPriceVariation
    ++ Alpha.encode message.financialInstrumentFullName
    ++ Alpha.encode message.partyRoleClearingOrg
    ++ encodeUIntLE 2 message.startDate
    ++ encodeUIntLE 2 message.endDate
    ++ Alpha.encode message.terminationType
    ++ encodeUInt 1 message.repoSubType
    ++ encodeUInt 1 message.moneyOrPar
    ++ encodeUInt 1 message.maxNoOfSubstitutions
    ++ Alpha.encode message.priceQuoteMethod
    ++ Alpha.encode message.userDefinedInstrument
    ++ Alpha.encode message.riskSet
    ++ Alpha.encode message.marketSet
    ++ encodeUIntLE 8 message.instrumentGuid
    ++ Alpha.encode message.termCode
    ++ encodeUInt 1 message.brokenDateTermType
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
    ++ encodeUInt 1 (BitVec.ofNat 8 message.repoUnderlyingsGroup.val.length)
    ++ encodeMany RepoUnderlyingsGroup.encode message.repoUnderlyingsGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.repoRelatedInstrumentsGroup.val.length)
    ++ encodeMany RepoRelatedInstrumentsGroup.encode message.repoRelatedInstrumentsGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.brokenDatesGroup.val.length)
    ++ encodeMany BrokenDatesGroup.encode message.brokenDatesGroup.val

def decode (bytes : List UInt8) : Option (MdInstrumentDefinitionRepo × List UInt8) := do
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
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (settlCurrency, bytes) ← Alpha.decode 3 bytes
  let (matchAlgorithm, bytes) ← Alpha.decode 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (maxTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (minPriceIncrementEx, bytes) ← decodeUIntLE 8 bytes
  let (displayFactor, bytes) ← decodeUIntLE 8 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 30 bytes
  let (unitOfMeasureQty, bytes) ← decodeUIntLE 8 bytes
  let (tradingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (financialInstrumentFullName, bytes) ← Alpha.decode 35 bytes
  let (partyRoleClearingOrg, bytes) ← Alpha.decode 5 bytes
  let (startDate, bytes) ← decodeUIntLE 2 bytes
  let (endDate, bytes) ← decodeUIntLE 2 bytes
  let (terminationType, bytes) ← Alpha.decode 8 bytes
  let (repoSubType, bytes) ← decodeUInt 1 bytes
  let (moneyOrPar, bytes) ← decodeUInt 1 bytes
  let (maxNoOfSubstitutions, bytes) ← decodeUInt 1 bytes
  let (priceQuoteMethod, bytes) ← Alpha.decode 5 bytes
  let (userDefinedInstrument, bytes) ← Alpha.decode 1 bytes
  let (riskSet, bytes) ← Alpha.decode 6 bytes
  let (marketSet, bytes) ← Alpha.decode 6 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
  let (termCode, bytes) ← Alpha.decode 20 bytes
  let (brokenDateTermType, bytes) ← decodeUInt 1 bytes
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
  let (repoUnderlyingsGroup_, bytes) ← decodeMany RepoUnderlyingsGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (repoRelatedInstrumentsGroup_, bytes) ← decodeMany RepoRelatedInstrumentsGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (brokenDatesGroup_, bytes) ← decodeMany BrokenDatesGroup.decode numInGroup.toNat bytes
  if fits_eventsGroup : eventsGroup_.length < 256 then
    if fits_feedTypesGroup : feedTypesGroup_.length < 256 then
      if fits_instAttribGroup : instAttribGroup_.length < 256 then
        if fits_lotTypeRulesGroup : lotTypeRulesGroup_.length < 256 then
          if fits_repoUnderlyingsGroup : repoUnderlyingsGroup_.length < 256 then
            if fits_repoRelatedInstrumentsGroup : repoRelatedInstrumentsGroup_.length < 256 then
              if fits_brokenDatesGroup : brokenDatesGroup_.length < 256 then
                pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, currency, settlCurrency, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementEx, displayFactor, unitOfMeasure, unitOfMeasureQty, tradingReferencePrice, tradingReferenceDate, highLimitPrice, lowLimitPrice, maxPriceVariation, financialInstrumentFullName, partyRoleClearingOrg, startDate, endDate, terminationType, repoSubType, moneyOrPar, maxNoOfSubstitutions, priceQuoteMethod, userDefinedInstrument, riskSet, marketSet, instrumentGuid, termCode, brokenDateTermType, blockLength, eventsGroup := ⟨eventsGroup_, fits_eventsGroup⟩, blockLength, feedTypesGroup := ⟨feedTypesGroup_, fits_feedTypesGroup⟩, blockLength, instAttribGroup := ⟨instAttribGroup_, fits_instAttribGroup⟩, blockLength, lotTypeRulesGroup := ⟨lotTypeRulesGroup_, fits_lotTypeRulesGroup⟩, blockLength, repoUnderlyingsGroup := ⟨repoUnderlyingsGroup_, fits_repoUnderlyingsGroup⟩, blockLength, repoRelatedInstrumentsGroup := ⟨repoRelatedInstrumentsGroup_, fits_repoRelatedInstrumentsGroup⟩, blockLength, brokenDatesGroup := ⟨brokenDatesGroup_, fits_brokenDatesGroup⟩ }, bytes)
              else none
            else none
          else none
        else none
      else none
    else none
  else none

@[simp] theorem decode_encode (message : MdInstrumentDefinitionRepo) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_eventsGroup : message.eventsGroup.val.length < 256 := by simpa using message.eventsGroup.length_lt
  have fits_feedTypesGroup : message.feedTypesGroup.val.length < 256 := by simpa using message.feedTypesGroup.length_lt
  have fits_instAttribGroup : message.instAttribGroup.val.length < 256 := by simpa using message.instAttribGroup.length_lt
  have fits_lotTypeRulesGroup : message.lotTypeRulesGroup.val.length < 256 := by simpa using message.lotTypeRulesGroup.length_lt
  have fits_repoUnderlyingsGroup : message.repoUnderlyingsGroup.val.length < 256 := by simpa using message.repoUnderlyingsGroup.length_lt
  have fits_repoRelatedInstrumentsGroup : message.repoRelatedInstrumentsGroup.val.length < 256 := by simpa using message.repoRelatedInstrumentsGroup.length_lt
  have fits_brokenDatesGroup : message.brokenDatesGroup.val.length < 256 := by simpa using message.brokenDatesGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_eventsGroup, fits_eventsGroup, decodeMany_encodeMany EventsGroup.encode EventsGroup.decode EventsGroup.decode_encode, Nat.mod_eq_of_lt fits_feedTypesGroup, fits_feedTypesGroup, decodeMany_encodeMany FeedTypesGroup.encode FeedTypesGroup.decode FeedTypesGroup.decode_encode, Nat.mod_eq_of_lt fits_instAttribGroup, fits_instAttribGroup, decodeMany_encodeMany InstAttribGroup.encode InstAttribGroup.decode InstAttribGroup.decode_encode, Nat.mod_eq_of_lt fits_lotTypeRulesGroup, fits_lotTypeRulesGroup, decodeMany_encodeMany LotTypeRulesGroup.encode LotTypeRulesGroup.decode LotTypeRulesGroup.decode_encode, Nat.mod_eq_of_lt fits_repoUnderlyingsGroup, fits_repoUnderlyingsGroup, decodeMany_encodeMany RepoUnderlyingsGroup.encode RepoUnderlyingsGroup.decode RepoUnderlyingsGroup.decode_encode, Nat.mod_eq_of_lt fits_repoRelatedInstrumentsGroup, fits_repoRelatedInstrumentsGroup, decodeMany_encodeMany RepoRelatedInstrumentsGroup.encode RepoRelatedInstrumentsGroup.decode RepoRelatedInstrumentsGroup.decode_encode, Nat.mod_eq_of_lt fits_brokenDatesGroup, fits_brokenDatesGroup, decodeMany_encodeMany BrokenDatesGroup.encode BrokenDatesGroup.decode BrokenDatesGroup.decode_encode]

end MdInstrumentDefinitionRepo

/-- Snapshot Refresh Top Orders Group: 29 bytes -/
structure SnapshotRefreshTopOrdersGroup where
  orderId : BitVec 64
  mdOrderPriority : BitVec 64
  mdEntryPxEx : BitVec 64
  mdDisplayQty : BitVec 32
  mdEntryTypeBook : MdEntryTypeBook
  deriving DecidableEq, Repr

namespace SnapshotRefreshTopOrdersGroup

def encode (message : SnapshotRefreshTopOrdersGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.mdOrderPriority
    ++ encodeUIntLE 8 message.mdEntryPxEx
    ++ encodeUIntLE 4 message.mdDisplayQty
    ++ MdEntryTypeBook.encode message.mdEntryTypeBook

def decode (bytes : List UInt8) : Option (SnapshotRefreshTopOrdersGroup × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (mdOrderPriority, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryPxEx, bytes) ← decodeUIntLE 8 bytes
  let (mdDisplayQty, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryTypeBook, bytes) ← MdEntryTypeBook.decode bytes
  pure ({ orderId, mdOrderPriority, mdEntryPxEx, mdDisplayQty, mdEntryTypeBook }, bytes)

@[simp] theorem encode_length (message : SnapshotRefreshTopOrdersGroup) : (encode message).length = 29 := by
  simp [encode]

theorem encode_length_pos (message : SnapshotRefreshTopOrdersGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SnapshotRefreshTopOrdersGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end SnapshotRefreshTopOrdersGroup

/-- Snapshot Refresh Top Orders -/
structure SnapshotRefreshTopOrders where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  securityId : BitVec 32
  blockLength : BitVec 16
  snapshotRefreshTopOrdersGroup : Bounded 1 SnapshotRefreshTopOrdersGroup
  deriving DecidableEq, Repr

namespace SnapshotRefreshTopOrders

def encode (message : SnapshotRefreshTopOrders) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.snapshotRefreshTopOrdersGroup.val.length)
    ++ encodeMany SnapshotRefreshTopOrdersGroup.encode message.snapshotRefreshTopOrdersGroup.val

def decode (bytes : List UInt8) : Option (SnapshotRefreshTopOrders × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotRefreshTopOrdersGroup_, bytes) ← decodeMany SnapshotRefreshTopOrdersGroup.decode numInGroup.toNat bytes
  if fits_snapshotRefreshTopOrdersGroup : snapshotRefreshTopOrdersGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, securityId, blockLength, snapshotRefreshTopOrdersGroup := ⟨snapshotRefreshTopOrdersGroup_, fits_snapshotRefreshTopOrdersGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : SnapshotRefreshTopOrders) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_snapshotRefreshTopOrdersGroup : message.snapshotRefreshTopOrdersGroup.val.length < 256 := by simpa using message.snapshotRefreshTopOrdersGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_snapshotRefreshTopOrdersGroup, fits_snapshotRefreshTopOrdersGroup, decodeMany_encodeMany SnapshotRefreshTopOrdersGroup.encode SnapshotRefreshTopOrdersGroup.decode SnapshotRefreshTopOrdersGroup.decode_encode]

end SnapshotRefreshTopOrders

/-- Security Status Workup Group: 10 bytes -/
structure SecurityStatusWorkupGroup where
  orderId : BitVec 64
  side : BitVec 8
  aggressorIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityStatusWorkupGroup

def encode (message : SecurityStatusWorkupGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.aggressorIndicator

def decode (bytes : List UInt8) : Option (SecurityStatusWorkupGroup × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (aggressorIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ orderId, side, aggressorIndicator }, bytes)

@[simp] theorem encode_length (message : SecurityStatusWorkupGroup) : (encode message).length = 10 := by
  simp [encode]

theorem encode_length_pos (message : SecurityStatusWorkupGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SecurityStatusWorkupGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end SecurityStatusWorkupGroup

/-- Security Status Workup -/
structure SecurityStatusWorkup where
  transactTime : BitVec 64
  mdEntryPxOptionalEx : BitVec 64
  securityId : BitVec 32
  matchEventIndicator : BitVec 8
  tradeDate : BitVec 16
  tradeLinkId : BitVec 32
  workupTradingStatus : BitVec 8
  haltReason : BitVec 8
  securityTradingEvent : BitVec 8
  blockLength : BitVec 16
  securityStatusWorkupGroup : Bounded 1 SecurityStatusWorkupGroup
  deriving DecidableEq, Repr

namespace SecurityStatusWorkup

def encode (message : SecurityStatusWorkup) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.mdEntryPxOptionalEx
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 2 message.tradeDate
    ++ encodeUIntLE 4 message.tradeLinkId
    ++ encodeUInt 1 message.workupTradingStatus
    ++ encodeUInt 1 message.haltReason
    ++ encodeUInt 1 message.securityTradingEvent
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.securityStatusWorkupGroup.val.length)
    ++ encodeMany SecurityStatusWorkupGroup.encode message.securityStatusWorkupGroup.val

def decode (bytes : List UInt8) : Option (SecurityStatusWorkup × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryPxOptionalEx, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (tradeLinkId, bytes) ← decodeUIntLE 4 bytes
  let (workupTradingStatus, bytes) ← decodeUInt 1 bytes
  let (haltReason, bytes) ← decodeUInt 1 bytes
  let (securityTradingEvent, bytes) ← decodeUInt 1 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityStatusWorkupGroup_, bytes) ← decodeMany SecurityStatusWorkupGroup.decode numInGroup.toNat bytes
  if fits_securityStatusWorkupGroup : securityStatusWorkupGroup_.length < 256 then
    pure ({ transactTime, mdEntryPxOptionalEx, securityId, matchEventIndicator, tradeDate, tradeLinkId, workupTradingStatus, haltReason, securityTradingEvent, blockLength, securityStatusWorkupGroup := ⟨securityStatusWorkupGroup_, fits_securityStatusWorkupGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : SecurityStatusWorkup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_securityStatusWorkupGroup : message.securityStatusWorkupGroup.val.length < 256 := by simpa using message.securityStatusWorkupGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_securityStatusWorkupGroup, fits_securityStatusWorkupGroup, decodeMany_encodeMany SecurityStatusWorkupGroup.encode SecurityStatusWorkupGroup.decode SecurityStatusWorkupGroup.decode_encode]

end SecurityStatusWorkup

/-- Snapshot Full Refresh Tcp Group: 26 bytes -/
structure SnapshotFullRefreshTcpGroup where
  mdEntryPxOptionalEx : BitVec 64
  mdEntrySizeShortOptional : BitVec 32
  tradeableSize : BitVec 32
  numberOfOrdersOptional : BitVec 32
  mdPriceLevelOptional : BitVec 8
  openCloseSettlFlag : BitVec 8
  mdEntryType : MdEntryType
  tradingReferenceDate : BitVec 16
  settlPriceType : BitVec 8
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshTcpGroup

def encode (message : SnapshotFullRefreshTcpGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxOptionalEx
    ++ encodeUIntLE 4 message.mdEntrySizeShortOptional
    ++ encodeUIntLE 4 message.tradeableSize
    ++ encodeUIntLE 4 message.numberOfOrdersOptional
    ++ encodeUInt 1 message.mdPriceLevelOptional
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ MdEntryType.encode message.mdEntryType
    ++ encodeUIntLE 2 message.tradingReferenceDate
    ++ encodeUIntLE 1 message.settlPriceType

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshTcpGroup × List UInt8) := do
  let (mdEntryPxOptionalEx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeShortOptional, bytes) ← decodeUIntLE 4 bytes
  let (tradeableSize, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrdersOptional, bytes) ← decodeUIntLE 4 bytes
  let (mdPriceLevelOptional, bytes) ← decodeUInt 1 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  pure ({ mdEntryPxOptionalEx, mdEntrySizeShortOptional, tradeableSize, numberOfOrdersOptional, mdPriceLevelOptional, openCloseSettlFlag, mdEntryType, tradingReferenceDate, settlPriceType }, bytes)

@[simp] theorem encode_length (message : SnapshotFullRefreshTcpGroup) : (encode message).length = 26 := by
  simp [encode]

theorem encode_length_pos (message : SnapshotFullRefreshTcpGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SnapshotFullRefreshTcpGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end SnapshotFullRefreshTcpGroup

/-- Snapshot Full Refresh Tcp -/
structure SnapshotFullRefreshTcp where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  securityId : BitVec 32
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  blockLength : BitVec 16
  snapshotFullRefreshTcpGroup : Bounded 1 SnapshotFullRefreshTcpGroup
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshTcp

def encode (message : SnapshotFullRefreshTcp) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 8 message.highLimitPrice
    ++ encodeUIntLE 8 message.lowLimitPrice
    ++ encodeUIntLE 8 message.maxPriceVariation
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.snapshotFullRefreshTcpGroup.val.length)
    ++ encodeMany SnapshotFullRefreshTcpGroup.encode message.snapshotFullRefreshTcpGroup.val

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshTcp × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotFullRefreshTcpGroup_, bytes) ← decodeMany SnapshotFullRefreshTcpGroup.decode numInGroup.toNat bytes
  if fits_snapshotFullRefreshTcpGroup : snapshotFullRefreshTcpGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, securityId, highLimitPrice, lowLimitPrice, maxPriceVariation, blockLength, snapshotFullRefreshTcpGroup := ⟨snapshotFullRefreshTcpGroup_, fits_snapshotFullRefreshTcpGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : SnapshotFullRefreshTcp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_snapshotFullRefreshTcpGroup : message.snapshotFullRefreshTcpGroup.val.length < 256 := by simpa using message.snapshotFullRefreshTcpGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_snapshotFullRefreshTcpGroup, fits_snapshotFullRefreshTcpGroup, decodeMany_encodeMany SnapshotFullRefreshTcpGroup.encode SnapshotFullRefreshTcpGroup.decode SnapshotFullRefreshTcpGroup.decode_encode]

end SnapshotFullRefreshTcp

/-- Collateral Market Value Group: 40 bytes -/
structure CollateralMarketValueGroup where
  underlyingSecurityAltId : Alpha 12
  underlyingSecurityAltIdSource : BitVec 8
  collateralMarketPrice : BitVec 64
  dirtyPrice : BitVec 64
  underlyingInstrumentGuid : BitVec 64
  mdStreamId : BitVec 8
  padding2 : Alpha 2
  deriving DecidableEq, Repr

namespace CollateralMarketValueGroup

def encode (message : CollateralMarketValueGroup) : List UInt8 :=
  Alpha.encode message.underlyingSecurityAltId
    ++ encodeUInt 1 message.underlyingSecurityAltIdSource
    ++ encodeUIntLE 8 message.collateralMarketPrice
    ++ encodeUIntLE 8 message.dirtyPrice
    ++ encodeUIntLE 8 message.underlyingInstrumentGuid
    ++ encodeUInt 1 message.mdStreamId
    ++ Alpha.encode message.padding2

def decode (bytes : List UInt8) : Option (CollateralMarketValueGroup × List UInt8) := do
  let (underlyingSecurityAltId, bytes) ← Alpha.decode 12 bytes
  let (underlyingSecurityAltIdSource, bytes) ← decodeUInt 1 bytes
  let (collateralMarketPrice, bytes) ← decodeUIntLE 8 bytes
  let (dirtyPrice, bytes) ← decodeUIntLE 8 bytes
  let (underlyingInstrumentGuid, bytes) ← decodeUIntLE 8 bytes
  let (mdStreamId, bytes) ← decodeUInt 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  pure ({ underlyingSecurityAltId, underlyingSecurityAltIdSource, collateralMarketPrice, dirtyPrice, underlyingInstrumentGuid, mdStreamId, padding2 }, bytes)

@[simp] theorem encode_length (message : CollateralMarketValueGroup) : (encode message).length = 40 := by
  simp [encode]

theorem encode_length_pos (message : CollateralMarketValueGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : CollateralMarketValueGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end CollateralMarketValueGroup

/-- Collateral Market Value -/
structure CollateralMarketValue where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  collateralMarketValueGroup : Bounded 1 CollateralMarketValueGroup
  deriving DecidableEq, Repr

namespace CollateralMarketValue

def encode (message : CollateralMarketValue) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.collateralMarketValueGroup.val.length)
    ++ encodeMany CollateralMarketValueGroup.encode message.collateralMarketValueGroup.val

def decode (bytes : List UInt8) : Option (CollateralMarketValue × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (collateralMarketValueGroup_, bytes) ← decodeMany CollateralMarketValueGroup.decode numInGroup.toNat bytes
  if fits_collateralMarketValueGroup : collateralMarketValueGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, padding2, blockLength, collateralMarketValueGroup := ⟨collateralMarketValueGroup_, fits_collateralMarketValueGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : CollateralMarketValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_collateralMarketValueGroup : message.collateralMarketValueGroup.val.length < 256 := by simpa using message.collateralMarketValueGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_collateralMarketValueGroup, fits_collateralMarketValueGroup, decodeMany_encodeMany CollateralMarketValueGroup.encode CollateralMarketValueGroup.decode CollateralMarketValueGroup.decode_encode]

end CollateralMarketValue

/-- Fx Lot Type Rules Group: 9 bytes -/
structure FxLotTypeRulesGroup where
  lotType : BitVec 8
  minLotSizeUInt64 : BitVec 64
  deriving DecidableEq, Repr

namespace FxLotTypeRulesGroup

def encode (message : FxLotTypeRulesGroup) : List UInt8 :=
  encodeUInt 1 message.lotType
    ++ encodeUIntLE 8 message.minLotSizeUInt64

def decode (bytes : List UInt8) : Option (FxLotTypeRulesGroup × List UInt8) := do
  let (lotType, bytes) ← decodeUInt 1 bytes
  let (minLotSizeUInt64, bytes) ← decodeUIntLE 8 bytes
  pure ({ lotType, minLotSizeUInt64 }, bytes)

@[simp] theorem encode_length (message : FxLotTypeRulesGroup) : (encode message).length = 9 := by
  simp [encode]

theorem encode_length_pos (message : FxLotTypeRulesGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : FxLotTypeRulesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end FxLotTypeRulesGroup

/-- Trading Sessions Group: 18 bytes -/
structure TradingSessionsGroup where
  tradeDate : BitVec 16
  settlDate : BitVec 16
  maturityDate : BitVec 16
  securityAltId : Alpha 12
  deriving DecidableEq, Repr

namespace TradingSessionsGroup

def encode (message : TradingSessionsGroup) : List UInt8 :=
  encodeUIntLE 2 message.tradeDate
    ++ encodeUIntLE 2 message.settlDate
    ++ encodeUIntLE 2 message.maturityDate
    ++ Alpha.encode message.securityAltId

def decode (bytes : List UInt8) : Option (TradingSessionsGroup × List UInt8) := do
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (settlDate, bytes) ← decodeUIntLE 2 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (securityAltId, bytes) ← Alpha.decode 12 bytes
  pure ({ tradeDate, settlDate, maturityDate, securityAltId }, bytes)

@[simp] theorem encode_length (message : TradingSessionsGroup) : (encode message).length = 18 := by
  simp [encode]

theorem encode_length_pos (message : TradingSessionsGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TradingSessionsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end TradingSessionsGroup

/-- Md Instrument Definition Fx -/
structure MdInstrumentDefinitionFx where
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
  currency : Alpha 3
  settlCurrency : Alpha 3
  priceQuoteCurrency : Alpha 3
  matchAlgorithm : Alpha 1
  minTradeVol : BitVec 32
  maxTradeVol : BitVec 32
  minPriceIncrementEx : BitVec 64
  displayFactor : BitVec 64
  pricePrecision : BitVec 8
  unitOfMeasure : Alpha 30
  unitOfMeasureQty : BitVec 64
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  userDefinedInstrument : Alpha 1
  financialInstrumentFullName : Alpha 35
  fxCurrencySymbol : Alpha 7
  settlType : Alpha 3
  interveningDays : BitVec 16
  fxBenchmarkRateFix : Alpha 20
  rateSource : Alpha 12
  fixRateLocalTime : Alpha 8
  fixRateLocalTimeZone : Alpha 20
  minQuoteLife : BitVec 32
  maxPriceDiscretionOffset : BitVec 64
  instrumentGuid : BitVec 64
  maturityMonthYear : MaturityMonthYear
  settlementLocale : Alpha 8
  altMinPriceIncrement : BitVec 64
  altMinQuoteLife : BitVec 32
  altPriceIncrementConstraint : BitVec 64
  maxBidAskConstraint : BitVec 64
  blockLength : BitVec 16
  eventsGroup : Bounded 1 EventsGroup
  blockLength : BitVec 16
  feedTypesGroup : Bounded 1 FeedTypesGroup
  blockLength : BitVec 16
  instAttribGroup : Bounded 1 InstAttribGroup
  blockLength : BitVec 16
  fxLotTypeRulesGroup : Bounded 1 FxLotTypeRulesGroup
  blockLength : BitVec 16
  tradingSessionsGroup : Bounded 1 TradingSessionsGroup
  deriving DecidableEq, Repr

namespace MdInstrumentDefinitionFx

def encode (message : MdInstrumentDefinitionFx) : List UInt8 :=
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
    ++ Alpha.encode message.currency
    ++ Alpha.encode message.settlCurrency
    ++ Alpha.encode message.priceQuoteCurrency
    ++ Alpha.encode message.matchAlgorithm
    ++ encodeUIntLE 4 message.minTradeVol
    ++ encodeUIntLE 4 message.maxTradeVol
    ++ encodeUIntLE 8 message.minPriceIncrementEx
    ++ encodeUIntLE 8 message.displayFactor
    ++ encodeUInt 1 message.pricePrecision
    ++ Alpha.encode message.unitOfMeasure
    ++ encodeUIntLE 8 message.unitOfMeasureQty
    ++ encodeUIntLE 8 message.highLimitPrice
    ++ encodeUIntLE 8 message.lowLimitPrice
    ++ encodeUIntLE 8 message.maxPriceVariation
    ++ Alpha.encode message.userDefinedInstrument
    ++ Alpha.encode message.financialInstrumentFullName
    ++ Alpha.encode message.fxCurrencySymbol
    ++ Alpha.encode message.settlType
    ++ encodeUIntLE 2 message.interveningDays
    ++ Alpha.encode message.fxBenchmarkRateFix
    ++ Alpha.encode message.rateSource
    ++ Alpha.encode message.fixRateLocalTime
    ++ Alpha.encode message.fixRateLocalTimeZone
    ++ encodeUIntLE 4 message.minQuoteLife
    ++ encodeUIntLE 8 message.maxPriceDiscretionOffset
    ++ encodeUIntLE 8 message.instrumentGuid
    ++ MaturityMonthYear.encode message.maturityMonthYear
    ++ Alpha.encode message.settlementLocale
    ++ encodeUIntLE 8 message.altMinPriceIncrement
    ++ encodeUIntLE 4 message.altMinQuoteLife
    ++ encodeUIntLE 8 message.altPriceIncrementConstraint
    ++ encodeUIntLE 8 message.maxBidAskConstraint
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
    ++ encodeUInt 1 (BitVec.ofNat 8 message.fxLotTypeRulesGroup.val.length)
    ++ encodeMany FxLotTypeRulesGroup.encode message.fxLotTypeRulesGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.tradingSessionsGroup.val.length)
    ++ encodeMany TradingSessionsGroup.encode message.tradingSessionsGroup.val

def decode (bytes : List UInt8) : Option (MdInstrumentDefinitionFx × List UInt8) := do
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
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (settlCurrency, bytes) ← Alpha.decode 3 bytes
  let (priceQuoteCurrency, bytes) ← Alpha.decode 3 bytes
  let (matchAlgorithm, bytes) ← Alpha.decode 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (maxTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (minPriceIncrementEx, bytes) ← decodeUIntLE 8 bytes
  let (displayFactor, bytes) ← decodeUIntLE 8 bytes
  let (pricePrecision, bytes) ← decodeUInt 1 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 30 bytes
  let (unitOfMeasureQty, bytes) ← decodeUIntLE 8 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (userDefinedInstrument, bytes) ← Alpha.decode 1 bytes
  let (financialInstrumentFullName, bytes) ← Alpha.decode 35 bytes
  let (fxCurrencySymbol, bytes) ← Alpha.decode 7 bytes
  let (settlType, bytes) ← Alpha.decode 3 bytes
  let (interveningDays, bytes) ← decodeUIntLE 2 bytes
  let (fxBenchmarkRateFix, bytes) ← Alpha.decode 20 bytes
  let (rateSource, bytes) ← Alpha.decode 12 bytes
  let (fixRateLocalTime, bytes) ← Alpha.decode 8 bytes
  let (fixRateLocalTimeZone, bytes) ← Alpha.decode 20 bytes
  let (minQuoteLife, bytes) ← decodeUIntLE 4 bytes
  let (maxPriceDiscretionOffset, bytes) ← decodeUIntLE 8 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (settlementLocale, bytes) ← Alpha.decode 8 bytes
  let (altMinPriceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (altMinQuoteLife, bytes) ← decodeUIntLE 4 bytes
  let (altPriceIncrementConstraint, bytes) ← decodeUIntLE 8 bytes
  let (maxBidAskConstraint, bytes) ← decodeUIntLE 8 bytes
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
  let (fxLotTypeRulesGroup_, bytes) ← decodeMany FxLotTypeRulesGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (tradingSessionsGroup_, bytes) ← decodeMany TradingSessionsGroup.decode numInGroup.toNat bytes
  if fits_eventsGroup : eventsGroup_.length < 256 then
    if fits_feedTypesGroup : feedTypesGroup_.length < 256 then
      if fits_instAttribGroup : instAttribGroup_.length < 256 then
        if fits_fxLotTypeRulesGroup : fxLotTypeRulesGroup_.length < 256 then
          if fits_tradingSessionsGroup : tradingSessionsGroup_.length < 256 then
            pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, currency, settlCurrency, priceQuoteCurrency, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementEx, displayFactor, pricePrecision, unitOfMeasure, unitOfMeasureQty, highLimitPrice, lowLimitPrice, maxPriceVariation, userDefinedInstrument, financialInstrumentFullName, fxCurrencySymbol, settlType, interveningDays, fxBenchmarkRateFix, rateSource, fixRateLocalTime, fixRateLocalTimeZone, minQuoteLife, maxPriceDiscretionOffset, instrumentGuid, maturityMonthYear, settlementLocale, altMinPriceIncrement, altMinQuoteLife, altPriceIncrementConstraint, maxBidAskConstraint, blockLength, eventsGroup := ⟨eventsGroup_, fits_eventsGroup⟩, blockLength, feedTypesGroup := ⟨feedTypesGroup_, fits_feedTypesGroup⟩, blockLength, instAttribGroup := ⟨instAttribGroup_, fits_instAttribGroup⟩, blockLength, fxLotTypeRulesGroup := ⟨fxLotTypeRulesGroup_, fits_fxLotTypeRulesGroup⟩, blockLength, tradingSessionsGroup := ⟨tradingSessionsGroup_, fits_tradingSessionsGroup⟩ }, bytes)
          else none
        else none
      else none
    else none
  else none

@[simp] theorem decode_encode (message : MdInstrumentDefinitionFx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_eventsGroup : message.eventsGroup.val.length < 256 := by simpa using message.eventsGroup.length_lt
  have fits_feedTypesGroup : message.feedTypesGroup.val.length < 256 := by simpa using message.feedTypesGroup.length_lt
  have fits_instAttribGroup : message.instAttribGroup.val.length < 256 := by simpa using message.instAttribGroup.length_lt
  have fits_fxLotTypeRulesGroup : message.fxLotTypeRulesGroup.val.length < 256 := by simpa using message.fxLotTypeRulesGroup.length_lt
  have fits_tradingSessionsGroup : message.tradingSessionsGroup.val.length < 256 := by simpa using message.tradingSessionsGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_eventsGroup, fits_eventsGroup, decodeMany_encodeMany EventsGroup.encode EventsGroup.decode EventsGroup.decode_encode, Nat.mod_eq_of_lt fits_feedTypesGroup, fits_feedTypesGroup, decodeMany_encodeMany FeedTypesGroup.encode FeedTypesGroup.decode FeedTypesGroup.decode_encode, Nat.mod_eq_of_lt fits_instAttribGroup, fits_instAttribGroup, decodeMany_encodeMany InstAttribGroup.encode InstAttribGroup.decode InstAttribGroup.decode_encode, Nat.mod_eq_of_lt fits_fxLotTypeRulesGroup, fits_fxLotTypeRulesGroup, decodeMany_encodeMany FxLotTypeRulesGroup.encode FxLotTypeRulesGroup.decode FxLotTypeRulesGroup.decode_encode, Nat.mod_eq_of_lt fits_tradingSessionsGroup, fits_tradingSessionsGroup, decodeMany_encodeMany TradingSessionsGroup.encode TradingSessionsGroup.decode TradingSessionsGroup.decode_encode]

end MdInstrumentDefinitionFx

/-- Incremental Refresh Book Long Group: 32 bytes -/
structure IncrementalRefreshBookLongGroup where
  mdEntryPxOptionalEx : BitVec 64
  mdEntrySizeOptional : BitVec 64
  securityId : BitVec 32
  rptSeq : BitVec 32
  numberOfOrdersOptional : BitVec 32
  mdPriceLevel : BitVec 8
  mdUpdateAction : BitVec 8
  mdEntryTypeBook : MdEntryTypeBook
  padding1 : Alpha 1
  deriving DecidableEq, Repr

namespace IncrementalRefreshBookLongGroup

def encode (message : IncrementalRefreshBookLongGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxOptionalEx
    ++ encodeUIntLE 8 message.mdEntrySizeOptional
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 4 message.numberOfOrdersOptional
    ++ encodeUInt 1 message.mdPriceLevel
    ++ encodeUInt 1 message.mdUpdateAction
    ++ MdEntryTypeBook.encode message.mdEntryTypeBook
    ++ Alpha.encode message.padding1

def decode (bytes : List UInt8) : Option (IncrementalRefreshBookLongGroup × List UInt8) := do
  let (mdEntryPxOptionalEx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrdersOptional, bytes) ← decodeUIntLE 4 bytes
  let (mdPriceLevel, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryTypeBook, bytes) ← MdEntryTypeBook.decode bytes
  let (padding1, bytes) ← Alpha.decode 1 bytes
  pure ({ mdEntryPxOptionalEx, mdEntrySizeOptional, securityId, rptSeq, numberOfOrdersOptional, mdPriceLevel, mdUpdateAction, mdEntryTypeBook, padding1 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshBookLongGroup) : (encode message).length = 32 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshBookLongGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshBookLongGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshBookLongGroup

/-- Incremental Refresh Book Long Order Id Group: 24 bytes -/
structure IncrementalRefreshBookLongOrderIdGroup where
  orderId : BitVec 64
  mdOrderPriorityOptional : BitVec 64
  mdDisplayQtyOptional : BitVec 32
  referenceId : BitVec 8
  orderUpdateAction : BitVec 8
  padding2 : Alpha 2
  deriving DecidableEq, Repr

namespace IncrementalRefreshBookLongOrderIdGroup

def encode (message : IncrementalRefreshBookLongOrderIdGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.mdOrderPriorityOptional
    ++ encodeUIntLE 4 message.mdDisplayQtyOptional
    ++ encodeUInt 1 message.referenceId
    ++ encodeUInt 1 message.orderUpdateAction
    ++ Alpha.encode message.padding2

def decode (bytes : List UInt8) : Option (IncrementalRefreshBookLongOrderIdGroup × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (mdOrderPriorityOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdDisplayQtyOptional, bytes) ← decodeUIntLE 4 bytes
  let (referenceId, bytes) ← decodeUInt 1 bytes
  let (orderUpdateAction, bytes) ← decodeUInt 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  pure ({ orderId, mdOrderPriorityOptional, mdDisplayQtyOptional, referenceId, orderUpdateAction, padding2 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshBookLongOrderIdGroup) : (encode message).length = 24 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshBookLongOrderIdGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshBookLongOrderIdGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshBookLongOrderIdGroup

/-- Md Incremental Refresh Book Long Qty -/
structure MdIncrementalRefreshBookLongQty where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  incrementalRefreshBookLongGroup : Bounded 1 IncrementalRefreshBookLongGroup
  blockLength : BitVec 16
  padding5 : Alpha 5
  incrementalRefreshBookLongOrderIdGroup : Bounded 1 IncrementalRefreshBookLongOrderIdGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshBookLongQty

def encode (message : MdIncrementalRefreshBookLongQty) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshBookLongGroup.val.length)
    ++ encodeMany IncrementalRefreshBookLongGroup.encode message.incrementalRefreshBookLongGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ Alpha.encode message.padding5
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshBookLongOrderIdGroup.val.length)
    ++ encodeMany IncrementalRefreshBookLongOrderIdGroup.encode message.incrementalRefreshBookLongOrderIdGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshBookLongQty × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshBookLongGroup_, bytes) ← decodeMany IncrementalRefreshBookLongGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshBookLongOrderIdGroup_, bytes) ← decodeMany IncrementalRefreshBookLongOrderIdGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshBookLongGroup : incrementalRefreshBookLongGroup_.length < 256 then
    if fits_incrementalRefreshBookLongOrderIdGroup : incrementalRefreshBookLongOrderIdGroup_.length < 256 then
      pure ({ transactTime, matchEventIndicator, padding2, blockLength, incrementalRefreshBookLongGroup := ⟨incrementalRefreshBookLongGroup_, fits_incrementalRefreshBookLongGroup⟩, blockLength, padding5, incrementalRefreshBookLongOrderIdGroup := ⟨incrementalRefreshBookLongOrderIdGroup_, fits_incrementalRefreshBookLongOrderIdGroup⟩ }, bytes)
    else none
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshBookLongQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshBookLongGroup : message.incrementalRefreshBookLongGroup.val.length < 256 := by simpa using message.incrementalRefreshBookLongGroup.length_lt
  have fits_incrementalRefreshBookLongOrderIdGroup : message.incrementalRefreshBookLongOrderIdGroup.val.length < 256 := by simpa using message.incrementalRefreshBookLongOrderIdGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshBookLongGroup, fits_incrementalRefreshBookLongGroup, decodeMany_encodeMany IncrementalRefreshBookLongGroup.encode IncrementalRefreshBookLongGroup.decode IncrementalRefreshBookLongGroup.decode_encode, Nat.mod_eq_of_lt fits_incrementalRefreshBookLongOrderIdGroup, fits_incrementalRefreshBookLongOrderIdGroup, decodeMany_encodeMany IncrementalRefreshBookLongOrderIdGroup.encode IncrementalRefreshBookLongOrderIdGroup.decode IncrementalRefreshBookLongOrderIdGroup.decode_encode]

end MdIncrementalRefreshBookLongQty

/-- Incremental Refresh Trade Summary Long Group: 40 bytes -/
structure IncrementalRefreshTradeSummaryLongGroup where
  mdEntryPxEx : BitVec 64
  mdEntrySize : BitVec 64
  securityId : BitVec 32
  rptSeq : BitVec 32
  numberOfOrders : BitVec 32
  mdTradeEntry : BitVec 32
  aggressorSide : BitVec 8
  mdUpdateAction : BitVec 8
  padding6 : Alpha 6
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeSummaryLongGroup

def encode (message : IncrementalRefreshTradeSummaryLongGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxEx
    ++ encodeUIntLE 8 message.mdEntrySize
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 4 message.numberOfOrders
    ++ encodeUIntLE 4 message.mdTradeEntry
    ++ encodeUInt 1 message.aggressorSide
    ++ encodeUInt 1 message.mdUpdateAction
    ++ Alpha.encode message.padding6

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeSummaryLongGroup × List UInt8) := do
  let (mdEntryPxEx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (mdTradeEntry, bytes) ← decodeUIntLE 4 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (padding6, bytes) ← Alpha.decode 6 bytes
  pure ({ mdEntryPxEx, mdEntrySize, securityId, rptSeq, numberOfOrders, mdTradeEntry, aggressorSide, mdUpdateAction, padding6 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshTradeSummaryLongGroup) : (encode message).length = 40 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryLongGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryLongGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshTradeSummaryLongGroup

/-- Incremental Refresh Trade Summary Long Order Id Group: 16 bytes -/
structure IncrementalRefreshTradeSummaryLongOrderIdGroup where
  orderId : BitVec 64
  lastQty : BitVec 32
  padding4 : Alpha 4
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeSummaryLongOrderIdGroup

def encode (message : IncrementalRefreshTradeSummaryLongOrderIdGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 4 message.lastQty
    ++ Alpha.encode message.padding4

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeSummaryLongOrderIdGroup × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (padding4, bytes) ← Alpha.decode 4 bytes
  pure ({ orderId, lastQty, padding4 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshTradeSummaryLongOrderIdGroup) : (encode message).length = 16 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryLongOrderIdGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryLongOrderIdGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshTradeSummaryLongOrderIdGroup

/-- Md Incremental Refresh Trade Summary Long Qty -/
structure MdIncrementalRefreshTradeSummaryLongQty where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  incrementalRefreshTradeSummaryLongGroup : Bounded 1 IncrementalRefreshTradeSummaryLongGroup
  blockLength : BitVec 16
  padding5 : Alpha 5
  incrementalRefreshTradeSummaryLongOrderIdGroup : Bounded 1 IncrementalRefreshTradeSummaryLongOrderIdGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshTradeSummaryLongQty

def encode (message : MdIncrementalRefreshTradeSummaryLongQty) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshTradeSummaryLongGroup.val.length)
    ++ encodeMany IncrementalRefreshTradeSummaryLongGroup.encode message.incrementalRefreshTradeSummaryLongGroup.val
    ++ encodeUIntLE 2 message.blockLength
    ++ Alpha.encode message.padding5
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshTradeSummaryLongOrderIdGroup.val.length)
    ++ encodeMany IncrementalRefreshTradeSummaryLongOrderIdGroup.encode message.incrementalRefreshTradeSummaryLongOrderIdGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshTradeSummaryLongQty × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTradeSummaryLongGroup_, bytes) ← decodeMany IncrementalRefreshTradeSummaryLongGroup.decode numInGroup.toNat bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTradeSummaryLongOrderIdGroup_, bytes) ← decodeMany IncrementalRefreshTradeSummaryLongOrderIdGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshTradeSummaryLongGroup : incrementalRefreshTradeSummaryLongGroup_.length < 256 then
    if fits_incrementalRefreshTradeSummaryLongOrderIdGroup : incrementalRefreshTradeSummaryLongOrderIdGroup_.length < 256 then
      pure ({ transactTime, matchEventIndicator, padding2, blockLength, incrementalRefreshTradeSummaryLongGroup := ⟨incrementalRefreshTradeSummaryLongGroup_, fits_incrementalRefreshTradeSummaryLongGroup⟩, blockLength, padding5, incrementalRefreshTradeSummaryLongOrderIdGroup := ⟨incrementalRefreshTradeSummaryLongOrderIdGroup_, fits_incrementalRefreshTradeSummaryLongOrderIdGroup⟩ }, bytes)
    else none
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshTradeSummaryLongQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshTradeSummaryLongGroup : message.incrementalRefreshTradeSummaryLongGroup.val.length < 256 := by simpa using message.incrementalRefreshTradeSummaryLongGroup.length_lt
  have fits_incrementalRefreshTradeSummaryLongOrderIdGroup : message.incrementalRefreshTradeSummaryLongOrderIdGroup.val.length < 256 := by simpa using message.incrementalRefreshTradeSummaryLongOrderIdGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshTradeSummaryLongGroup, fits_incrementalRefreshTradeSummaryLongGroup, decodeMany_encodeMany IncrementalRefreshTradeSummaryLongGroup.encode IncrementalRefreshTradeSummaryLongGroup.decode IncrementalRefreshTradeSummaryLongGroup.decode_encode, Nat.mod_eq_of_lt fits_incrementalRefreshTradeSummaryLongOrderIdGroup, fits_incrementalRefreshTradeSummaryLongOrderIdGroup, decodeMany_encodeMany IncrementalRefreshTradeSummaryLongOrderIdGroup.encode IncrementalRefreshTradeSummaryLongOrderIdGroup.decode IncrementalRefreshTradeSummaryLongOrderIdGroup.decode_encode]

end MdIncrementalRefreshTradeSummaryLongQty

/-- Incremental Refresh Volume Long Group: 24 bytes -/
structure IncrementalRefreshVolumeLongGroup where
  mdEntrySize : BitVec 64
  securityId : BitVec 32
  rptSeq : BitVec 32
  mdUpdateAction : BitVec 8
  padding7 : Alpha 7
  deriving DecidableEq, Repr

namespace IncrementalRefreshVolumeLongGroup

def encode (message : IncrementalRefreshVolumeLongGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntrySize
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUInt 1 message.mdUpdateAction
    ++ Alpha.encode message.padding7

def decode (bytes : List UInt8) : Option (IncrementalRefreshVolumeLongGroup × List UInt8) := do
  let (mdEntrySize, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (padding7, bytes) ← Alpha.decode 7 bytes
  pure ({ mdEntrySize, securityId, rptSeq, mdUpdateAction, padding7 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshVolumeLongGroup) : (encode message).length = 24 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshVolumeLongGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshVolumeLongGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshVolumeLongGroup

/-- Md Incremental Refresh Volume Long Qty -/
structure MdIncrementalRefreshVolumeLongQty where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  incrementalRefreshVolumeLongGroup : Bounded 1 IncrementalRefreshVolumeLongGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshVolumeLongQty

def encode (message : MdIncrementalRefreshVolumeLongQty) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshVolumeLongGroup.val.length)
    ++ encodeMany IncrementalRefreshVolumeLongGroup.encode message.incrementalRefreshVolumeLongGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshVolumeLongQty × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshVolumeLongGroup_, bytes) ← decodeMany IncrementalRefreshVolumeLongGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshVolumeLongGroup : incrementalRefreshVolumeLongGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, padding2, blockLength, incrementalRefreshVolumeLongGroup := ⟨incrementalRefreshVolumeLongGroup_, fits_incrementalRefreshVolumeLongGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshVolumeLongQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshVolumeLongGroup : message.incrementalRefreshVolumeLongGroup.val.length < 256 := by simpa using message.incrementalRefreshVolumeLongGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshVolumeLongGroup, fits_incrementalRefreshVolumeLongGroup, decodeMany_encodeMany IncrementalRefreshVolumeLongGroup.encode IncrementalRefreshVolumeLongGroup.decode IncrementalRefreshVolumeLongGroup.decode_encode]

end MdIncrementalRefreshVolumeLongQty

/-- Incremental Refresh Session Statistics Long Group: 32 bytes -/
structure IncrementalRefreshSessionStatisticsLongGroup where
  mdEntryPxEx : BitVec 64
  mdEntrySizeOptional : BitVec 64
  securityId : BitVec 32
  rptSeq : BitVec 32
  openCloseSettlFlag : BitVec 8
  mdUpdateAction : BitVec 8
  mdEntryTypeStatistics : MdEntryTypeStatistics
  padding5 : Alpha 5
  deriving DecidableEq, Repr

namespace IncrementalRefreshSessionStatisticsLongGroup

def encode (message : IncrementalRefreshSessionStatisticsLongGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxEx
    ++ encodeUIntLE 8 message.mdEntrySizeOptional
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ encodeUInt 1 message.mdUpdateAction
    ++ MdEntryTypeStatistics.encode message.mdEntryTypeStatistics
    ++ Alpha.encode message.padding5

def decode (bytes : List UInt8) : Option (IncrementalRefreshSessionStatisticsLongGroup × List UInt8) := do
  let (mdEntryPxEx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryTypeStatistics, bytes) ← MdEntryTypeStatistics.decode bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  pure ({ mdEntryPxEx, mdEntrySizeOptional, securityId, rptSeq, openCloseSettlFlag, mdUpdateAction, mdEntryTypeStatistics, padding5 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshSessionStatisticsLongGroup) : (encode message).length = 32 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshSessionStatisticsLongGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshSessionStatisticsLongGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshSessionStatisticsLongGroup

/-- Md Incremental Refresh Session Statistics Long Qty -/
structure MdIncrementalRefreshSessionStatisticsLongQty where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  blockLength : BitVec 16
  incrementalRefreshSessionStatisticsLongGroup : Bounded 1 IncrementalRefreshSessionStatisticsLongGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshSessionStatisticsLongQty

def encode (message : MdIncrementalRefreshSessionStatisticsLongQty) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshSessionStatisticsLongGroup.val.length)
    ++ encodeMany IncrementalRefreshSessionStatisticsLongGroup.encode message.incrementalRefreshSessionStatisticsLongGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshSessionStatisticsLongQty × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshSessionStatisticsLongGroup_, bytes) ← decodeMany IncrementalRefreshSessionStatisticsLongGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshSessionStatisticsLongGroup : incrementalRefreshSessionStatisticsLongGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, padding2, blockLength, incrementalRefreshSessionStatisticsLongGroup := ⟨incrementalRefreshSessionStatisticsLongGroup_, fits_incrementalRefreshSessionStatisticsLongGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshSessionStatisticsLongQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshSessionStatisticsLongGroup : message.incrementalRefreshSessionStatisticsLongGroup.val.length < 256 := by simpa using message.incrementalRefreshSessionStatisticsLongGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshSessionStatisticsLongGroup, fits_incrementalRefreshSessionStatisticsLongGroup, decodeMany_encodeMany IncrementalRefreshSessionStatisticsLongGroup.encode IncrementalRefreshSessionStatisticsLongGroup.decode IncrementalRefreshSessionStatisticsLongGroup.decode_encode]

end MdIncrementalRefreshSessionStatisticsLongQty

/-- Snapshotfull Refresh Tcp Long Group: 23 bytes -/
structure SnapshotfullRefreshTcpLongGroup where
  mdEntryPxOptionalEx : BitVec 64
  mdEntrySizeOptional : BitVec 64
  numberOfOrdersOptional : BitVec 32
  mdPriceLevelUnsignedOptional : BitVec 8
  openCloseSettlFlag : BitVec 8
  mdEntryType : MdEntryType
  deriving DecidableEq, Repr

namespace SnapshotfullRefreshTcpLongGroup

def encode (message : SnapshotfullRefreshTcpLongGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxOptionalEx
    ++ encodeUIntLE 8 message.mdEntrySizeOptional
    ++ encodeUIntLE 4 message.numberOfOrdersOptional
    ++ encodeUInt 1 message.mdPriceLevelUnsignedOptional
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ MdEntryType.encode message.mdEntryType

def decode (bytes : List UInt8) : Option (SnapshotfullRefreshTcpLongGroup × List UInt8) := do
  let (mdEntryPxOptionalEx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 8 bytes
  let (numberOfOrdersOptional, bytes) ← decodeUIntLE 4 bytes
  let (mdPriceLevelUnsignedOptional, bytes) ← decodeUInt 1 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  pure ({ mdEntryPxOptionalEx, mdEntrySizeOptional, numberOfOrdersOptional, mdPriceLevelUnsignedOptional, openCloseSettlFlag, mdEntryType }, bytes)

@[simp] theorem encode_length (message : SnapshotfullRefreshTcpLongGroup) : (encode message).length = 23 := by
  simp [encode]

theorem encode_length_pos (message : SnapshotfullRefreshTcpLongGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SnapshotfullRefreshTcpLongGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end SnapshotfullRefreshTcpLongGroup

/-- Snapshot Full Refresh Tcp Long Qty -/
structure SnapshotFullRefreshTcpLongQty where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  securityId : BitVec 32
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  blockLength : BitVec 16
  snapshotfullRefreshTcpLongGroup : Bounded 1 SnapshotfullRefreshTcpLongGroup
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshTcpLongQty

def encode (message : SnapshotFullRefreshTcpLongQty) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 8 message.highLimitPrice
    ++ encodeUIntLE 8 message.lowLimitPrice
    ++ encodeUIntLE 8 message.maxPriceVariation
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.snapshotfullRefreshTcpLongGroup.val.length)
    ++ encodeMany SnapshotfullRefreshTcpLongGroup.encode message.snapshotfullRefreshTcpLongGroup.val

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshTcpLongQty × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotfullRefreshTcpLongGroup_, bytes) ← decodeMany SnapshotfullRefreshTcpLongGroup.decode numInGroup.toNat bytes
  if fits_snapshotfullRefreshTcpLongGroup : snapshotfullRefreshTcpLongGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, securityId, highLimitPrice, lowLimitPrice, maxPriceVariation, blockLength, snapshotfullRefreshTcpLongGroup := ⟨snapshotfullRefreshTcpLongGroup_, fits_snapshotfullRefreshTcpLongGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : SnapshotFullRefreshTcpLongQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_snapshotfullRefreshTcpLongGroup : message.snapshotfullRefreshTcpLongGroup.val.length < 256 := by simpa using message.snapshotfullRefreshTcpLongGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_snapshotfullRefreshTcpLongGroup, fits_snapshotfullRefreshTcpLongGroup, decodeMany_encodeMany SnapshotfullRefreshTcpLongGroup.encode SnapshotfullRefreshTcpLongGroup.decode SnapshotfullRefreshTcpLongGroup.decode_encode]

end SnapshotFullRefreshTcpLongQty

/-- Snapshot Full Refresh Long Group: 23 bytes -/
structure SnapshotFullRefreshLongGroup where
  mdEntryPxOptionalEx : BitVec 64
  mdEntrySizeOptional : BitVec 64
  numberOfOrdersOptional : BitVec 32
  mdPriceLevelUnsignedOptional : BitVec 8
  openCloseSettlFlag : BitVec 8
  mdEntryType : MdEntryType
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshLongGroup

def encode (message : SnapshotFullRefreshLongGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxOptionalEx
    ++ encodeUIntLE 8 message.mdEntrySizeOptional
    ++ encodeUIntLE 4 message.numberOfOrdersOptional
    ++ encodeUInt 1 message.mdPriceLevelUnsignedOptional
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ MdEntryType.encode message.mdEntryType

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshLongGroup × List UInt8) := do
  let (mdEntryPxOptionalEx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 8 bytes
  let (numberOfOrdersOptional, bytes) ← decodeUIntLE 4 bytes
  let (mdPriceLevelUnsignedOptional, bytes) ← decodeUInt 1 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  pure ({ mdEntryPxOptionalEx, mdEntrySizeOptional, numberOfOrdersOptional, mdPriceLevelUnsignedOptional, openCloseSettlFlag, mdEntryType }, bytes)

@[simp] theorem encode_length (message : SnapshotFullRefreshLongGroup) : (encode message).length = 23 := by
  simp [encode]

theorem encode_length_pos (message : SnapshotFullRefreshLongGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SnapshotFullRefreshLongGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end SnapshotFullRefreshLongGroup

/-- Snapshot Full Refresh Long Qty -/
structure SnapshotFullRefreshLongQty where
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
  snapshotFullRefreshLongGroup : Bounded 1 SnapshotFullRefreshLongGroup
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshLongQty

def encode (message : SnapshotFullRefreshLongQty) : List UInt8 :=
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
    ++ encodeUInt 1 (BitVec.ofNat 8 message.snapshotFullRefreshLongGroup.val.length)
    ++ encodeMany SnapshotFullRefreshLongGroup.encode message.snapshotFullRefreshLongGroup.val

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshLongQty × List UInt8) := do
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
  let (snapshotFullRefreshLongGroup_, bytes) ← decodeMany SnapshotFullRefreshLongGroup.decode numInGroup.toNat bytes
  if fits_snapshotFullRefreshLongGroup : snapshotFullRefreshLongGroup_.length < 256 then
    pure ({ lastMsgSeqNumProcessed, totNumReports, securityId, rptSeq, transactTime, lastUpdateTime, tradeDate, mdSecurityTradingStatus, highLimitPrice, lowLimitPrice, maxPriceVariation, blockLength, snapshotFullRefreshLongGroup := ⟨snapshotFullRefreshLongGroup_, fits_snapshotFullRefreshLongGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : SnapshotFullRefreshLongQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_snapshotFullRefreshLongGroup : message.snapshotFullRefreshLongGroup.val.length < 256 := by simpa using message.snapshotFullRefreshLongGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_snapshotFullRefreshLongGroup, fits_snapshotFullRefreshLongGroup, decodeMany_encodeMany SnapshotFullRefreshLongGroup.encode SnapshotFullRefreshLongGroup.decode SnapshotFullRefreshLongGroup.decode_encode]

end SnapshotFullRefreshLongQty

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
  | securityStatus (message : SecurityStatus) -- 30
  | mdIncrementalRefreshVolume (message : MdIncrementalRefreshVolume) -- 37
  | quoteRequest (message : QuoteRequest) -- 39
  | mdIncrementalRefreshBook (message : MdIncrementalRefreshBook) -- 46
  | mdIncrementalRefreshOrderBook (message : MdIncrementalRefreshOrderBook) -- 47
  | mdIncrementalRefreshTradeSummary (message : MdIncrementalRefreshTradeSummary) -- 48
  | mdIncrementalRefreshDailyStatistics (message : MdIncrementalRefreshDailyStatistics) -- 49
  | mdIncrementalRefreshLimitsBanding (message : MdIncrementalRefreshLimitsBanding) -- 50
  | mdIncrementalRefreshSessionStatistics (message : MdIncrementalRefreshSessionStatistics) -- 51
  | snapshotFullRefresh (message : SnapshotFullRefresh) -- 52
  | snapshotFullRefreshOrderBook (message : SnapshotFullRefreshOrderBook) -- 53
  | mdInstrumentDefinitionFuture (message : MdInstrumentDefinitionFuture) -- 54
  | mdInstrumentDefinitionOption (message : MdInstrumentDefinitionOption) -- 55
  | mdInstrumentDefinitionSpread (message : MdInstrumentDefinitionSpread) -- 56
  | mdInstrumentDefinitionFixedIncome (message : MdInstrumentDefinitionFixedIncome) -- 57
  | mdInstrumentDefinitionRepo (message : MdInstrumentDefinitionRepo) -- 58
  | snapshotRefreshTopOrders (message : SnapshotRefreshTopOrders) -- 59
  | securityStatusWorkup (message : SecurityStatusWorkup) -- 60
  | snapshotFullRefreshTcp (message : SnapshotFullRefreshTcp) -- 61
  | collateralMarketValue (message : CollateralMarketValue) -- 62
  | mdInstrumentDefinitionFx (message : MdInstrumentDefinitionFx) -- 63
  | mdIncrementalRefreshBookLongQty (message : MdIncrementalRefreshBookLongQty) -- 64
  | mdIncrementalRefreshTradeSummaryLongQty (message : MdIncrementalRefreshTradeSummaryLongQty) -- 65
  | mdIncrementalRefreshVolumeLongQty (message : MdIncrementalRefreshVolumeLongQty) -- 66
  | mdIncrementalRefreshSessionStatisticsLongQty (message : MdIncrementalRefreshSessionStatisticsLongQty) -- 67
  | snapshotFullRefreshTcpLongQty (message : SnapshotFullRefreshTcpLongQty) -- 68
  | snapshotFullRefreshLongQty (message : SnapshotFullRefreshLongQty) -- 69
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
  | .securityStatus _ => 30
  | .mdIncrementalRefreshVolume _ => 37
  | .quoteRequest _ => 39
  | .mdIncrementalRefreshBook _ => 46
  | .mdIncrementalRefreshOrderBook _ => 47
  | .mdIncrementalRefreshTradeSummary _ => 48
  | .mdIncrementalRefreshDailyStatistics _ => 49
  | .mdIncrementalRefreshLimitsBanding _ => 50
  | .mdIncrementalRefreshSessionStatistics _ => 51
  | .snapshotFullRefresh _ => 52
  | .snapshotFullRefreshOrderBook _ => 53
  | .mdInstrumentDefinitionFuture _ => 54
  | .mdInstrumentDefinitionOption _ => 55
  | .mdInstrumentDefinitionSpread _ => 56
  | .mdInstrumentDefinitionFixedIncome _ => 57
  | .mdInstrumentDefinitionRepo _ => 58
  | .snapshotRefreshTopOrders _ => 59
  | .securityStatusWorkup _ => 60
  | .snapshotFullRefreshTcp _ => 61
  | .collateralMarketValue _ => 62
  | .mdInstrumentDefinitionFx _ => 63
  | .mdIncrementalRefreshBookLongQty _ => 64
  | .mdIncrementalRefreshTradeSummaryLongQty _ => 65
  | .mdIncrementalRefreshVolumeLongQty _ => 66
  | .mdIncrementalRefreshSessionStatisticsLongQty _ => 67
  | .snapshotFullRefreshTcpLongQty _ => 68
  | .snapshotFullRefreshLongQty _ => 69
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
  | .securityStatus message => SecurityStatus.encode message
  | .mdIncrementalRefreshVolume message => MdIncrementalRefreshVolume.encode message
  | .quoteRequest message => QuoteRequest.encode message
  | .mdIncrementalRefreshBook message => MdIncrementalRefreshBook.encode message
  | .mdIncrementalRefreshOrderBook message => MdIncrementalRefreshOrderBook.encode message
  | .mdIncrementalRefreshTradeSummary message => MdIncrementalRefreshTradeSummary.encode message
  | .mdIncrementalRefreshDailyStatistics message => MdIncrementalRefreshDailyStatistics.encode message
  | .mdIncrementalRefreshLimitsBanding message => MdIncrementalRefreshLimitsBanding.encode message
  | .mdIncrementalRefreshSessionStatistics message => MdIncrementalRefreshSessionStatistics.encode message
  | .snapshotFullRefresh message => SnapshotFullRefresh.encode message
  | .snapshotFullRefreshOrderBook message => SnapshotFullRefreshOrderBook.encode message
  | .mdInstrumentDefinitionFuture message => MdInstrumentDefinitionFuture.encode message
  | .mdInstrumentDefinitionOption message => MdInstrumentDefinitionOption.encode message
  | .mdInstrumentDefinitionSpread message => MdInstrumentDefinitionSpread.encode message
  | .mdInstrumentDefinitionFixedIncome message => MdInstrumentDefinitionFixedIncome.encode message
  | .mdInstrumentDefinitionRepo message => MdInstrumentDefinitionRepo.encode message
  | .snapshotRefreshTopOrders message => SnapshotRefreshTopOrders.encode message
  | .securityStatusWorkup message => SecurityStatusWorkup.encode message
  | .snapshotFullRefreshTcp message => SnapshotFullRefreshTcp.encode message
  | .collateralMarketValue message => CollateralMarketValue.encode message
  | .mdInstrumentDefinitionFx message => MdInstrumentDefinitionFx.encode message
  | .mdIncrementalRefreshBookLongQty message => MdIncrementalRefreshBookLongQty.encode message
  | .mdIncrementalRefreshTradeSummaryLongQty message => MdIncrementalRefreshTradeSummaryLongQty.encode message
  | .mdIncrementalRefreshVolumeLongQty message => MdIncrementalRefreshVolumeLongQty.encode message
  | .mdIncrementalRefreshSessionStatisticsLongQty message => MdIncrementalRefreshSessionStatisticsLongQty.encode message
  | .snapshotFullRefreshTcpLongQty message => SnapshotFullRefreshTcpLongQty.encode message
  | .snapshotFullRefreshLongQty message => SnapshotFullRefreshLongQty.encode message
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
  else if tag = 30 then (SecurityStatus.decode bytes).map fun (message, rest) => (.securityStatus message, rest)
  else if tag = 37 then (MdIncrementalRefreshVolume.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshVolume message, rest)
  else if tag = 39 then (QuoteRequest.decode bytes).map fun (message, rest) => (.quoteRequest message, rest)
  else if tag = 46 then (MdIncrementalRefreshBook.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshBook message, rest)
  else if tag = 47 then (MdIncrementalRefreshOrderBook.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshOrderBook message, rest)
  else if tag = 48 then (MdIncrementalRefreshTradeSummary.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshTradeSummary message, rest)
  else if tag = 49 then (MdIncrementalRefreshDailyStatistics.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshDailyStatistics message, rest)
  else if tag = 50 then (MdIncrementalRefreshLimitsBanding.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshLimitsBanding message, rest)
  else if tag = 51 then (MdIncrementalRefreshSessionStatistics.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshSessionStatistics message, rest)
  else if tag = 52 then (SnapshotFullRefresh.decode bytes).map fun (message, rest) => (.snapshotFullRefresh message, rest)
  else if tag = 53 then (SnapshotFullRefreshOrderBook.decode bytes).map fun (message, rest) => (.snapshotFullRefreshOrderBook message, rest)
  else if tag = 54 then (MdInstrumentDefinitionFuture.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionFuture message, rest)
  else if tag = 55 then (MdInstrumentDefinitionOption.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionOption message, rest)
  else if tag = 56 then (MdInstrumentDefinitionSpread.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionSpread message, rest)
  else if tag = 57 then (MdInstrumentDefinitionFixedIncome.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionFixedIncome message, rest)
  else if tag = 58 then (MdInstrumentDefinitionRepo.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionRepo message, rest)
  else if tag = 59 then (SnapshotRefreshTopOrders.decode bytes).map fun (message, rest) => (.snapshotRefreshTopOrders message, rest)
  else if tag = 60 then (SecurityStatusWorkup.decode bytes).map fun (message, rest) => (.securityStatusWorkup message, rest)
  else if tag = 61 then (SnapshotFullRefreshTcp.decode bytes).map fun (message, rest) => (.snapshotFullRefreshTcp message, rest)
  else if tag = 62 then (CollateralMarketValue.decode bytes).map fun (message, rest) => (.collateralMarketValue message, rest)
  else if tag = 63 then (MdInstrumentDefinitionFx.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionFx message, rest)
  else if tag = 64 then (MdIncrementalRefreshBookLongQty.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshBookLongQty message, rest)
  else if tag = 65 then (MdIncrementalRefreshTradeSummaryLongQty.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshTradeSummaryLongQty message, rest)
  else if tag = 66 then (MdIncrementalRefreshVolumeLongQty.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshVolumeLongQty message, rest)
  else if tag = 67 then (MdIncrementalRefreshSessionStatisticsLongQty.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshSessionStatisticsLongQty message, rest)
  else if tag = 68 then (SnapshotFullRefreshTcpLongQty.decode bytes).map fun (message, rest) => (.snapshotFullRefreshTcpLongQty message, rest)
  else if tag = 69 then (SnapshotFullRefreshLongQty.decode bytes).map fun (message, rest) => (.snapshotFullRefreshLongQty message, rest)
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
  | securityStatus inner =>
    simp [encodeBody, h, ServerPayload.encode, SecurityStatus.encode]
  | mdIncrementalRefreshVolume inner =>
    have bound_mdIncrementalRefreshVolume_incrementalRefreshVolumeGroup := inner.incrementalRefreshVolumeGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshVolume.encode, encodeMany_length_const IncrementalRefreshVolumeGroup.encode 16 IncrementalRefreshVolumeGroup.encode_length]
    omega
  | quoteRequest inner =>
    have bound_quoteRequest_relatedSymGroup := inner.relatedSymGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, QuoteRequest.encode, encodeMany_length_const RelatedSymGroup.encode 32 RelatedSymGroup.encode_length]
    omega
  | mdIncrementalRefreshBook inner =>
    have bound_mdIncrementalRefreshBook_incrementalRefreshBookGroup := inner.incrementalRefreshBookGroup.length_lt
    have bound_mdIncrementalRefreshBook_incrementalRefreshBookOrderIdGroup := inner.incrementalRefreshBookOrderIdGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshBook.encode, encodeMany_length_const IncrementalRefreshBookGroup.encode 32 IncrementalRefreshBookGroup.encode_length, encodeMany_length_const IncrementalRefreshBookOrderIdGroup.encode 24 IncrementalRefreshBookOrderIdGroup.encode_length]
    omega
  | mdIncrementalRefreshOrderBook inner =>
    have bound_mdIncrementalRefreshOrderBook_incrementalRefreshOrderBookGroup := inner.incrementalRefreshOrderBookGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshOrderBook.encode, encodeMany_length_const IncrementalRefreshOrderBookGroup.encode 40 IncrementalRefreshOrderBookGroup.encode_length]
    omega
  | mdIncrementalRefreshTradeSummary inner =>
    have bound_mdIncrementalRefreshTradeSummary_incrementalRefreshTradeSummaryGroup := inner.incrementalRefreshTradeSummaryGroup.length_lt
    have bound_mdIncrementalRefreshTradeSummary_incrementalRefreshTradeSummaryOrderIdGroup := inner.incrementalRefreshTradeSummaryOrderIdGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshTradeSummary.encode, encodeMany_length_const IncrementalRefreshTradeSummaryGroup.encode 32 IncrementalRefreshTradeSummaryGroup.encode_length, encodeMany_length_const IncrementalRefreshTradeSummaryOrderIdGroup.encode 16 IncrementalRefreshTradeSummaryOrderIdGroup.encode_length]
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
  | snapshotFullRefresh inner =>
    have bound_snapshotFullRefresh_snapshotFullRefreshGroup := inner.snapshotFullRefreshGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, SnapshotFullRefresh.encode, encodeMany_length_const SnapshotFullRefreshGroup.encode 22 SnapshotFullRefreshGroup.encode_length]
    omega
  | snapshotFullRefreshOrderBook inner =>
    have bound_snapshotFullRefreshOrderBook_snapshotFullRefreshOrderBookGroup := inner.snapshotFullRefreshOrderBookGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, SnapshotFullRefreshOrderBook.encode, encodeMany_length_const SnapshotFullRefreshOrderBookGroup.encode 29 SnapshotFullRefreshOrderBookGroup.encode_length]
    omega
  | mdInstrumentDefinitionFuture inner =>
    have bound_mdInstrumentDefinitionFuture_eventsGroup := inner.eventsGroup.length_lt
    have bound_mdInstrumentDefinitionFuture_feedTypesGroup := inner.feedTypesGroup.length_lt
    have bound_mdInstrumentDefinitionFuture_instAttribGroup := inner.instAttribGroup.length_lt
    have bound_mdInstrumentDefinitionFuture_lotTypeRulesGroup := inner.lotTypeRulesGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdInstrumentDefinitionFuture.encode, encodeMany_length_const EventsGroup.encode 9 EventsGroup.encode_length, encodeMany_length_const FeedTypesGroup.encode 4 FeedTypesGroup.encode_length, encodeMany_length_const InstAttribGroup.encode 4 InstAttribGroup.encode_length, encodeMany_length_const LotTypeRulesGroup.encode 5 LotTypeRulesGroup.encode_length]
    omega
  | mdInstrumentDefinitionOption inner =>
    have bound_mdInstrumentDefinitionOption_eventsGroup := inner.eventsGroup.length_lt
    have bound_mdInstrumentDefinitionOption_feedTypesGroup := inner.feedTypesGroup.length_lt
    have bound_mdInstrumentDefinitionOption_instAttribGroup := inner.instAttribGroup.length_lt
    have bound_mdInstrumentDefinitionOption_lotTypeRulesGroup := inner.lotTypeRulesGroup.length_lt
    have bound_mdInstrumentDefinitionOption_optionUnderlyingsGroup := inner.optionUnderlyingsGroup.length_lt
    have bound_mdInstrumentDefinitionOption_optionRelatedInstrumentsGroup := inner.optionRelatedInstrumentsGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdInstrumentDefinitionOption.encode, encodeMany_length_const EventsGroup.encode 9 EventsGroup.encode_length, encodeMany_length_const FeedTypesGroup.encode 4 FeedTypesGroup.encode_length, encodeMany_length_const InstAttribGroup.encode 4 InstAttribGroup.encode_length, encodeMany_length_const LotTypeRulesGroup.encode 5 LotTypeRulesGroup.encode_length, encodeMany_length_const OptionUnderlyingsGroup.encode 24 OptionUnderlyingsGroup.encode_length, encodeMany_length_const OptionRelatedInstrumentsGroup.encode 24 OptionRelatedInstrumentsGroup.encode_length]
    omega
  | mdInstrumentDefinitionSpread inner =>
    have bound_mdInstrumentDefinitionSpread_eventsGroup := inner.eventsGroup.length_lt
    have bound_mdInstrumentDefinitionSpread_feedTypesGroup := inner.feedTypesGroup.length_lt
    have bound_mdInstrumentDefinitionSpread_instAttribGroup := inner.instAttribGroup.length_lt
    have bound_mdInstrumentDefinitionSpread_lotTypeRulesGroup := inner.lotTypeRulesGroup.length_lt
    have bound_mdInstrumentDefinitionSpread_legsGroup := inner.legsGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdInstrumentDefinitionSpread.encode, encodeMany_length_const EventsGroup.encode 9 EventsGroup.encode_length, encodeMany_length_const FeedTypesGroup.encode 4 FeedTypesGroup.encode_length, encodeMany_length_const InstAttribGroup.encode 4 InstAttribGroup.encode_length, encodeMany_length_const LotTypeRulesGroup.encode 5 LotTypeRulesGroup.encode_length, encodeMany_length_const LegsGroup.encode 18 LegsGroup.encode_length]
    omega
  | mdInstrumentDefinitionFixedIncome inner =>
    have bound_mdInstrumentDefinitionFixedIncome_eventsGroup := inner.eventsGroup.length_lt
    have bound_mdInstrumentDefinitionFixedIncome_feedTypesGroup := inner.feedTypesGroup.length_lt
    have bound_mdInstrumentDefinitionFixedIncome_instAttribGroup := inner.instAttribGroup.length_lt
    have bound_mdInstrumentDefinitionFixedIncome_lotTypeRulesGroup := inner.lotTypeRulesGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdInstrumentDefinitionFixedIncome.encode, encodeMany_length_const EventsGroup.encode 9 EventsGroup.encode_length, encodeMany_length_const FeedTypesGroup.encode 4 FeedTypesGroup.encode_length, encodeMany_length_const InstAttribGroup.encode 4 InstAttribGroup.encode_length, encodeMany_length_const LotTypeRulesGroup.encode 5 LotTypeRulesGroup.encode_length]
    omega
  | mdInstrumentDefinitionRepo inner =>
    have bound_mdInstrumentDefinitionRepo_eventsGroup := inner.eventsGroup.length_lt
    have bound_mdInstrumentDefinitionRepo_feedTypesGroup := inner.feedTypesGroup.length_lt
    have bound_mdInstrumentDefinitionRepo_instAttribGroup := inner.instAttribGroup.length_lt
    have bound_mdInstrumentDefinitionRepo_lotTypeRulesGroup := inner.lotTypeRulesGroup.length_lt
    have bound_mdInstrumentDefinitionRepo_repoUnderlyingsGroup := inner.repoUnderlyingsGroup.length_lt
    have bound_mdInstrumentDefinitionRepo_repoRelatedInstrumentsGroup := inner.repoRelatedInstrumentsGroup.length_lt
    have bound_mdInstrumentDefinitionRepo_brokenDatesGroup := inner.brokenDatesGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdInstrumentDefinitionRepo.encode, encodeMany_length_const EventsGroup.encode 9 EventsGroup.encode_length, encodeMany_length_const FeedTypesGroup.encode 4 FeedTypesGroup.encode_length, encodeMany_length_const InstAttribGroup.encode 4 InstAttribGroup.encode_length, encodeMany_length_const LotTypeRulesGroup.encode 5 LotTypeRulesGroup.encode_length, encodeMany_length_const RepoUnderlyingsGroup.encode 118 RepoUnderlyingsGroup.encode_length, encodeMany_length_const RepoRelatedInstrumentsGroup.encode 32 RepoRelatedInstrumentsGroup.encode_length, encodeMany_length_const BrokenDatesGroup.encode 16 BrokenDatesGroup.encode_length]
    omega
  | snapshotRefreshTopOrders inner =>
    have bound_snapshotRefreshTopOrders_snapshotRefreshTopOrdersGroup := inner.snapshotRefreshTopOrdersGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, SnapshotRefreshTopOrders.encode, encodeMany_length_const SnapshotRefreshTopOrdersGroup.encode 29 SnapshotRefreshTopOrdersGroup.encode_length]
    omega
  | securityStatusWorkup inner =>
    have bound_securityStatusWorkup_securityStatusWorkupGroup := inner.securityStatusWorkupGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, SecurityStatusWorkup.encode, encodeMany_length_const SecurityStatusWorkupGroup.encode 10 SecurityStatusWorkupGroup.encode_length]
    omega
  | snapshotFullRefreshTcp inner =>
    have bound_snapshotFullRefreshTcp_snapshotFullRefreshTcpGroup := inner.snapshotFullRefreshTcpGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, SnapshotFullRefreshTcp.encode, encodeMany_length_const SnapshotFullRefreshTcpGroup.encode 26 SnapshotFullRefreshTcpGroup.encode_length]
    omega
  | collateralMarketValue inner =>
    have bound_collateralMarketValue_collateralMarketValueGroup := inner.collateralMarketValueGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, CollateralMarketValue.encode, encodeMany_length_const CollateralMarketValueGroup.encode 40 CollateralMarketValueGroup.encode_length]
    omega
  | mdInstrumentDefinitionFx inner =>
    have bound_mdInstrumentDefinitionFx_eventsGroup := inner.eventsGroup.length_lt
    have bound_mdInstrumentDefinitionFx_feedTypesGroup := inner.feedTypesGroup.length_lt
    have bound_mdInstrumentDefinitionFx_instAttribGroup := inner.instAttribGroup.length_lt
    have bound_mdInstrumentDefinitionFx_fxLotTypeRulesGroup := inner.fxLotTypeRulesGroup.length_lt
    have bound_mdInstrumentDefinitionFx_tradingSessionsGroup := inner.tradingSessionsGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdInstrumentDefinitionFx.encode, encodeMany_length_const EventsGroup.encode 9 EventsGroup.encode_length, encodeMany_length_const FeedTypesGroup.encode 4 FeedTypesGroup.encode_length, encodeMany_length_const InstAttribGroup.encode 4 InstAttribGroup.encode_length, encodeMany_length_const FxLotTypeRulesGroup.encode 9 FxLotTypeRulesGroup.encode_length, encodeMany_length_const TradingSessionsGroup.encode 18 TradingSessionsGroup.encode_length]
    omega
  | mdIncrementalRefreshBookLongQty inner =>
    have bound_mdIncrementalRefreshBookLongQty_incrementalRefreshBookLongGroup := inner.incrementalRefreshBookLongGroup.length_lt
    have bound_mdIncrementalRefreshBookLongQty_incrementalRefreshBookLongOrderIdGroup := inner.incrementalRefreshBookLongOrderIdGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshBookLongQty.encode, encodeMany_length_const IncrementalRefreshBookLongGroup.encode 32 IncrementalRefreshBookLongGroup.encode_length, encodeMany_length_const IncrementalRefreshBookLongOrderIdGroup.encode 24 IncrementalRefreshBookLongOrderIdGroup.encode_length]
    omega
  | mdIncrementalRefreshTradeSummaryLongQty inner =>
    have bound_mdIncrementalRefreshTradeSummaryLongQty_incrementalRefreshTradeSummaryLongGroup := inner.incrementalRefreshTradeSummaryLongGroup.length_lt
    have bound_mdIncrementalRefreshTradeSummaryLongQty_incrementalRefreshTradeSummaryLongOrderIdGroup := inner.incrementalRefreshTradeSummaryLongOrderIdGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshTradeSummaryLongQty.encode, encodeMany_length_const IncrementalRefreshTradeSummaryLongGroup.encode 40 IncrementalRefreshTradeSummaryLongGroup.encode_length, encodeMany_length_const IncrementalRefreshTradeSummaryLongOrderIdGroup.encode 16 IncrementalRefreshTradeSummaryLongOrderIdGroup.encode_length]
    omega
  | mdIncrementalRefreshVolumeLongQty inner =>
    have bound_mdIncrementalRefreshVolumeLongQty_incrementalRefreshVolumeLongGroup := inner.incrementalRefreshVolumeLongGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshVolumeLongQty.encode, encodeMany_length_const IncrementalRefreshVolumeLongGroup.encode 24 IncrementalRefreshVolumeLongGroup.encode_length]
    omega
  | mdIncrementalRefreshSessionStatisticsLongQty inner =>
    have bound_mdIncrementalRefreshSessionStatisticsLongQty_incrementalRefreshSessionStatisticsLongGroup := inner.incrementalRefreshSessionStatisticsLongGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, MdIncrementalRefreshSessionStatisticsLongQty.encode, encodeMany_length_const IncrementalRefreshSessionStatisticsLongGroup.encode 32 IncrementalRefreshSessionStatisticsLongGroup.encode_length]
    omega
  | snapshotFullRefreshTcpLongQty inner =>
    have bound_snapshotFullRefreshTcpLongQty_snapshotfullRefreshTcpLongGroup := inner.snapshotfullRefreshTcpLongGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, SnapshotFullRefreshTcpLongQty.encode, encodeMany_length_const SnapshotfullRefreshTcpLongGroup.encode 23 SnapshotfullRefreshTcpLongGroup.encode_length]
    omega
  | snapshotFullRefreshLongQty inner =>
    have bound_snapshotFullRefreshLongQty_snapshotFullRefreshLongGroup := inner.snapshotFullRefreshLongGroup.length_lt
    simp [encodeBody, h, ServerPayload.encode, SnapshotFullRefreshLongQty.encode, encodeMany_length_const SnapshotFullRefreshLongGroup.encode 23 SnapshotFullRefreshLongGroup.encode_length]
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

end Omi.CmeGlobexMdp3SbeV113ServerTcp
