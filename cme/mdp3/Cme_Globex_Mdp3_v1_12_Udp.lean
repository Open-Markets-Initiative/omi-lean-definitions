import Omi.Wire

/-!
# CME Group Market Data Platform 3 v1.12

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

namespace Omi.CmeGlobexMdp3SbeV112Udp

/-- Md Entry Type Book: one byte code -/
def MdEntryTypeBook.codes : List UInt8 :=
  [0x30, 0x31, 0x45, 0x46, 0x4A, 0x77, 0x78]

inductive MdEntryTypeBook where
  | bid -- Bid
  | offer -- Offer
  | impliedBid -- Implied Bid
  | impliedOffer -- Implied Offer
  | bookReset -- Book Reset
  | marketBestOffer -- Market Best Offer
  | marketBestBid -- Market Best Bid
  | unlisted (byte : { byte : UInt8 // byte ∉ MdEntryTypeBook.codes }) -- any other code, kept as it is
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
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MdEntryTypeBook :=
  if byte = 0x30 then .bid
  else if byte = 0x31 then .offer
  else if byte = 0x45 then .impliedBid
  else if byte = 0x46 then .impliedOffer
  else if byte = 0x4A then .bookReset
  else if byte = 0x77 then .marketBestOffer
  else .marketBestBid

def ofByte (byte : UInt8) : MdEntryTypeBook :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MdEntryTypeBook) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | offer => decide
  | impliedBid => decide
  | impliedOffer => decide
  | bookReset => decide
  | marketBestOffer => decide
  | marketBestBid => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MdEntryTypeBook) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeBook × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeBook) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeBook) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MdEntryTypeBook

/-- Md Entry Type Daily Statistics: one byte code -/
def MdEntryTypeDailyStatistics.codes : List UInt8 :=
  [0x36, 0x42, 0x43, 0x57]

inductive MdEntryTypeDailyStatistics where
  | settlementPrice -- Settlement Price
  | clearedVolume -- Cleared Volume
  | openInterest -- Open Interest
  | fixingPrice -- Fixing Price
  | unlisted (byte : { byte : UInt8 // byte ∉ MdEntryTypeDailyStatistics.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MdEntryTypeDailyStatistics

def toByte : MdEntryTypeDailyStatistics → UInt8
  | .settlementPrice => 0x36
  | .clearedVolume => 0x42
  | .openInterest => 0x43
  | .fixingPrice => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MdEntryTypeDailyStatistics :=
  if byte = 0x36 then .settlementPrice
  else if byte = 0x42 then .clearedVolume
  else if byte = 0x43 then .openInterest
  else .fixingPrice

def ofByte (byte : UInt8) : MdEntryTypeDailyStatistics :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MdEntryTypeDailyStatistics) : ofByte value.toByte = value := by
  cases value with
  | settlementPrice => decide
  | clearedVolume => decide
  | openInterest => decide
  | fixingPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MdEntryTypeDailyStatistics) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeDailyStatistics × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeDailyStatistics) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeDailyStatistics) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MdEntryTypeDailyStatistics

/-- Md Entry Type Statistics: one byte code -/
def MdEntryTypeStatistics.codes : List UInt8 :=
  [0x34, 0x37, 0x38, 0x39, 0x4E, 0x4F]

inductive MdEntryTypeStatistics where
  | openPrice -- Open Price
  | highTrade -- High Trade
  | lowTrade -- Low Trade
  | vwap -- Vwap
  | highestBid -- Highest Bid
  | lowestOffer -- Lowest Offer
  | unlisted (byte : { byte : UInt8 // byte ∉ MdEntryTypeStatistics.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MdEntryTypeStatistics

def toByte : MdEntryTypeStatistics → UInt8
  | .openPrice => 0x34
  | .highTrade => 0x37
  | .lowTrade => 0x38
  | .vwap => 0x39
  | .highestBid => 0x4E
  | .lowestOffer => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MdEntryTypeStatistics :=
  if byte = 0x34 then .openPrice
  else if byte = 0x37 then .highTrade
  else if byte = 0x38 then .lowTrade
  else if byte = 0x39 then .vwap
  else if byte = 0x4E then .highestBid
  else .lowestOffer

def ofByte (byte : UInt8) : MdEntryTypeStatistics :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MdEntryTypeStatistics) : ofByte value.toByte = value := by
  cases value with
  | openPrice => decide
  | highTrade => decide
  | lowTrade => decide
  | vwap => decide
  | highestBid => decide
  | lowestOffer => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MdEntryTypeStatistics) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeStatistics × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeStatistics) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeStatistics) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MdEntryTypeStatistics

/-- Md Entry Type: one byte code -/
def MdEntryType.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x34, 0x36, 0x37, 0x38, 0x39, 0x42, 0x43, 0x45, 0x46, 0x4A, 0x4E, 0x4F, 0x57, 0x65, 0x67, 0x77, 0x78]

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
  | unlisted (byte : { byte : UInt8 // byte ∉ MdEntryType.codes }) -- any other code, kept as it is
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
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MdEntryType :=
  if byte = 0x30 then .bid
  else if byte = 0x31 then .offer
  else if byte = 0x32 then .trade
  else if byte = 0x34 then .openPrice
  else if byte = 0x36 then .settlementPrice
  else if byte = 0x37 then .tradingSessionHighPrice
  else if byte = 0x38 then .tradingSessionLowPrice
  else if byte = 0x39 then .vwap
  else if byte = 0x42 then .clearedVolume
  else if byte = 0x43 then .openInterest
  else if byte = 0x45 then .impliedBid
  else if byte = 0x46 then .impliedOffer
  else if byte = 0x4A then .bookReset
  else if byte = 0x4E then .sessionHighBid
  else if byte = 0x4F then .sessionLowOffer
  else if byte = 0x57 then .fixingPrice
  else if byte = 0x65 then .electronicVolume
  else if byte = 0x67 then .thresholdLimitsandPriceBandVariation
  else if byte = 0x77 then .marketBestOffer
  else .marketBestBid

def ofByte (byte : UInt8) : MdEntryType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MdEntryType) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | offer => decide
  | trade => decide
  | openPrice => decide
  | settlementPrice => decide
  | tradingSessionHighPrice => decide
  | tradingSessionLowPrice => decide
  | vwap => decide
  | clearedVolume => decide
  | openInterest => decide
  | impliedBid => decide
  | impliedOffer => decide
  | bookReset => decide
  | sessionHighBid => decide
  | sessionLowOffer => decide
  | fixingPrice => decide
  | electronicVolume => decide
  | thresholdLimitsandPriceBandVariation => decide
  | marketBestOffer => decide
  | marketBestBid => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MdEntryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MdEntryType

/-- Security Update Action: one byte code -/
def SecurityUpdateAction.codes : List UInt8 :=
  [0x41, 0x44, 0x4D]

inductive SecurityUpdateAction where
  | add -- Add
  | delete -- Delete
  | modify -- Modify
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityUpdateAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityUpdateAction

def toByte : SecurityUpdateAction → UInt8
  | .add => 0x41
  | .delete => 0x44
  | .modify => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityUpdateAction :=
  if byte = 0x41 then .add
  else if byte = 0x44 then .delete
  else .modify

def ofByte (byte : UInt8) : SecurityUpdateAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityUpdateAction) : ofByte value.toByte = value := by
  cases value with
  | add => decide
  | delete => decide
  | modify => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityUpdateAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityUpdateAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityUpdateAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityUpdateAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityUpdateAction

/-- Binary Packet Header: 12 bytes -/
structure BinaryPacketHeader where
  packetSequenceNumber : BitVec 32
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace BinaryPacketHeader

def encode (message : BinaryPacketHeader) : List UInt8 :=
  encodeUIntLE 4 message.packetSequenceNumber
    ++ encodeUIntLE 8 message.sendingTime

def decode (bytes : List UInt8) : Option (BinaryPacketHeader × List UInt8) := do
  let (packetSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ packetSequenceNumber, sendingTime }, bytes)

@[simp] theorem encode_length (message : BinaryPacketHeader) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BinaryPacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BinaryPacketHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end BinaryPacketHeader

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
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : ChannelResetGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ChannelResetGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end ChannelResetGroup

/-- Channel Reset Groups -/
structure ChannelResetGroups where
  blockLength : BitVec 16
  channelResetGroup : Bounded 1 ChannelResetGroup
  deriving DecidableEq, Repr

namespace ChannelResetGroups

def encode (message : ChannelResetGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.channelResetGroup.val.length)
    ++ encodeMany ChannelResetGroup.encode message.channelResetGroup.val

def decode (bytes : List UInt8) : Option (ChannelResetGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (channelResetGroup_, bytes) ← decodeMany ChannelResetGroup.decode numInGroup.toNat bytes
  if fits_channelResetGroup : channelResetGroup_.length < 256 ^ 1 then
    pure ({ blockLength, channelResetGroup := ⟨channelResetGroup_, fits_channelResetGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ChannelResetGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ChannelResetGroups) : (encode message).length ≤ 513 := by
  have bound_channelResetGroup := message.channelResetGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const ChannelResetGroup.encode 2 ChannelResetGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : ChannelResetGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 ChannelResetGroup.encode ChannelResetGroup.decode ChannelResetGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.channelResetGroup.length_lt, ↓reduceDIte]
  rfl

end ChannelResetGroups

/-- Channel Reset -/
structure ChannelReset where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  channelResetGroups : ChannelResetGroups
  deriving DecidableEq, Repr

namespace ChannelReset

def encode (message : ChannelReset) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ ChannelResetGroups.encode message.channelResetGroups

def decode (bytes : List UInt8) : Option (ChannelReset × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (channelResetGroups, bytes) ← ChannelResetGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, channelResetGroups }, bytes)

theorem encode_length_pos (message : ChannelReset) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ChannelReset) : (encode message).length ≤ 522 := by
  have bound_channelResetGroups := ChannelResetGroups.encode_length_le message.channelResetGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : ChannelReset) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ChannelResetGroups.decode_encode, Option.bind_some]
  rfl

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
  simp [decode, encode]

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
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : AdminLogin) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdminLogin) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

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
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : AdminLogout) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdminLogout) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatus) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshVolumeGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshVolumeGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshVolumeGroup

/-- Incremental Refresh Volume Groups -/
structure IncrementalRefreshVolumeGroups where
  blockLength : BitVec 16
  incrementalRefreshVolumeGroup : Bounded 1 IncrementalRefreshVolumeGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshVolumeGroups

def encode (message : IncrementalRefreshVolumeGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshVolumeGroup.val.length)
    ++ encodeMany IncrementalRefreshVolumeGroup.encode message.incrementalRefreshVolumeGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshVolumeGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshVolumeGroup_, bytes) ← decodeMany IncrementalRefreshVolumeGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshVolumeGroup : incrementalRefreshVolumeGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshVolumeGroup := ⟨incrementalRefreshVolumeGroup_, fits_incrementalRefreshVolumeGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshVolumeGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshVolumeGroups) : (encode message).length ≤ 4083 := by
  have bound_incrementalRefreshVolumeGroup := message.incrementalRefreshVolumeGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshVolumeGroup.encode 16 IncrementalRefreshVolumeGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshVolumeGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshVolumeGroup.encode IncrementalRefreshVolumeGroup.decode IncrementalRefreshVolumeGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshVolumeGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshVolumeGroups

/-- Md Incremental Refresh Volume -/
structure MdIncrementalRefreshVolume where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshVolumeGroups : IncrementalRefreshVolumeGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshVolume

def encode (message : MdIncrementalRefreshVolume) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ IncrementalRefreshVolumeGroups.encode message.incrementalRefreshVolumeGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshVolume × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshVolumeGroups, bytes) ← IncrementalRefreshVolumeGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshVolumeGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshVolume) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshVolume) : (encode message).length ≤ 4094 := by
  have bound_incrementalRefreshVolumeGroups := IncrementalRefreshVolumeGroups.encode_length_le message.incrementalRefreshVolumeGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshVolume) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshVolumeGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RelatedSymGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RelatedSymGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end RelatedSymGroup

/-- Related Sym Groups -/
structure RelatedSymGroups where
  blockLength : BitVec 16
  relatedSymGroup : Bounded 1 RelatedSymGroup
  deriving DecidableEq, Repr

namespace RelatedSymGroups

def encode (message : RelatedSymGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.relatedSymGroup.val.length)
    ++ encodeMany RelatedSymGroup.encode message.relatedSymGroup.val

def decode (bytes : List UInt8) : Option (RelatedSymGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (relatedSymGroup_, bytes) ← decodeMany RelatedSymGroup.decode numInGroup.toNat bytes
  if fits_relatedSymGroup : relatedSymGroup_.length < 256 ^ 1 then
    pure ({ blockLength, relatedSymGroup := ⟨relatedSymGroup_, fits_relatedSymGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : RelatedSymGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RelatedSymGroups) : (encode message).length ≤ 8163 := by
  have bound_relatedSymGroup := message.relatedSymGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const RelatedSymGroup.encode 32 RelatedSymGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : RelatedSymGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 RelatedSymGroup.encode RelatedSymGroup.decode RelatedSymGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.relatedSymGroup.length_lt, ↓reduceDIte]
  rfl

end RelatedSymGroups

/-- Quote Request -/
structure QuoteRequest where
  transactTime : BitVec 64
  quoteReqId : Alpha 23
  matchEventIndicator : BitVec 8
  padding3 : Alpha 3
  relatedSymGroups : RelatedSymGroups
  deriving DecidableEq, Repr

namespace QuoteRequest

def encode (message : QuoteRequest) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ Alpha.encode message.quoteReqId
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding3
    ++ RelatedSymGroups.encode message.relatedSymGroups

def decode (bytes : List UInt8) : Option (QuoteRequest × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteReqId, bytes) ← Alpha.decode 23 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding3, bytes) ← Alpha.decode 3 bytes
  let (relatedSymGroups, bytes) ← RelatedSymGroups.decode bytes
  pure ({ transactTime, quoteReqId, matchEventIndicator, padding3, relatedSymGroups }, bytes)

theorem encode_length_pos (message : QuoteRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteRequest) : (encode message).length ≤ 8198 := by
  have bound_relatedSymGroups := RelatedSymGroups.encode_length_le message.relatedSymGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RelatedSymGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryTypeBook.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshBookGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshBookGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MdEntryTypeBook.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshBookGroup

/-- Incremental Refresh Book Groups -/
structure IncrementalRefreshBookGroups where
  blockLength : BitVec 16
  incrementalRefreshBookGroup : Bounded 1 IncrementalRefreshBookGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshBookGroups

def encode (message : IncrementalRefreshBookGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshBookGroup.val.length)
    ++ encodeMany IncrementalRefreshBookGroup.encode message.incrementalRefreshBookGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshBookGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshBookGroup_, bytes) ← decodeMany IncrementalRefreshBookGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshBookGroup : incrementalRefreshBookGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshBookGroup := ⟨incrementalRefreshBookGroup_, fits_incrementalRefreshBookGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshBookGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshBookGroups) : (encode message).length ≤ 8163 := by
  have bound_incrementalRefreshBookGroup := message.incrementalRefreshBookGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshBookGroup.encode 32 IncrementalRefreshBookGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshBookGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshBookGroup.encode IncrementalRefreshBookGroup.decode IncrementalRefreshBookGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshBookGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshBookGroups

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshBookOrderIdGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshBookOrderIdGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshBookOrderIdGroup

/-- Incremental Refresh Book Order Id Groups -/
structure IncrementalRefreshBookOrderIdGroups where
  blockLength : BitVec 16
  padding5 : Alpha 5
  incrementalRefreshBookOrderIdGroup : Bounded 1 IncrementalRefreshBookOrderIdGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshBookOrderIdGroups

def encode (message : IncrementalRefreshBookOrderIdGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ Alpha.encode message.padding5
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshBookOrderIdGroup.val.length)
    ++ encodeMany IncrementalRefreshBookOrderIdGroup.encode message.incrementalRefreshBookOrderIdGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshBookOrderIdGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshBookOrderIdGroup_, bytes) ← decodeMany IncrementalRefreshBookOrderIdGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshBookOrderIdGroup : incrementalRefreshBookOrderIdGroup_.length < 256 ^ 1 then
    pure ({ blockLength, padding5, incrementalRefreshBookOrderIdGroup := ⟨incrementalRefreshBookOrderIdGroup_, fits_incrementalRefreshBookOrderIdGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshBookOrderIdGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshBookOrderIdGroups) : (encode message).length ≤ 6128 := by
  have bound_incrementalRefreshBookOrderIdGroup := message.incrementalRefreshBookOrderIdGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshBookOrderIdGroup.encode 24 IncrementalRefreshBookOrderIdGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshBookOrderIdGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshBookOrderIdGroup.encode IncrementalRefreshBookOrderIdGroup.decode IncrementalRefreshBookOrderIdGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshBookOrderIdGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshBookOrderIdGroups

/-- Md Incremental Refresh Book -/
structure MdIncrementalRefreshBook where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshBookGroups : IncrementalRefreshBookGroups
  incrementalRefreshBookOrderIdGroups : IncrementalRefreshBookOrderIdGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshBook

def encode (message : MdIncrementalRefreshBook) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ IncrementalRefreshBookGroups.encode message.incrementalRefreshBookGroups
    ++ IncrementalRefreshBookOrderIdGroups.encode message.incrementalRefreshBookOrderIdGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshBook × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshBookGroups, bytes) ← IncrementalRefreshBookGroups.decode bytes
  let (incrementalRefreshBookOrderIdGroups, bytes) ← IncrementalRefreshBookOrderIdGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshBookGroups, incrementalRefreshBookOrderIdGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshBook) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshBook) : (encode message).length ≤ 14302 := by
  have bound_incrementalRefreshBookGroups := IncrementalRefreshBookGroups.encode_length_le message.incrementalRefreshBookGroups
  have bound_incrementalRefreshBookOrderIdGroups := IncrementalRefreshBookOrderIdGroups.encode_length_le message.incrementalRefreshBookOrderIdGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshBook) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshBookGroups.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshBookOrderIdGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryTypeBook.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshOrderBookGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshOrderBookGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MdEntryTypeBook.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshOrderBookGroup

/-- Incremental Refresh Order Book Groups -/
structure IncrementalRefreshOrderBookGroups where
  blockLength : BitVec 16
  incrementalRefreshOrderBookGroup : Bounded 1 IncrementalRefreshOrderBookGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshOrderBookGroups

def encode (message : IncrementalRefreshOrderBookGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshOrderBookGroup.val.length)
    ++ encodeMany IncrementalRefreshOrderBookGroup.encode message.incrementalRefreshOrderBookGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshOrderBookGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshOrderBookGroup_, bytes) ← decodeMany IncrementalRefreshOrderBookGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshOrderBookGroup : incrementalRefreshOrderBookGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshOrderBookGroup := ⟨incrementalRefreshOrderBookGroup_, fits_incrementalRefreshOrderBookGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshOrderBookGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshOrderBookGroups) : (encode message).length ≤ 10203 := by
  have bound_incrementalRefreshOrderBookGroup := message.incrementalRefreshOrderBookGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshOrderBookGroup.encode 40 IncrementalRefreshOrderBookGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshOrderBookGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshOrderBookGroup.encode IncrementalRefreshOrderBookGroup.decode IncrementalRefreshOrderBookGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshOrderBookGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshOrderBookGroups

/-- Md Incremental Refresh Order Book -/
structure MdIncrementalRefreshOrderBook where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshOrderBookGroups : IncrementalRefreshOrderBookGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshOrderBook

def encode (message : MdIncrementalRefreshOrderBook) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ IncrementalRefreshOrderBookGroups.encode message.incrementalRefreshOrderBookGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshOrderBook × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshOrderBookGroups, bytes) ← IncrementalRefreshOrderBookGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshOrderBookGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshOrderBook) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshOrderBook) : (encode message).length ≤ 10214 := by
  have bound_incrementalRefreshOrderBookGroups := IncrementalRefreshOrderBookGroups.encode_length_le message.incrementalRefreshOrderBookGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshOrderBook) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshOrderBookGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshTradeSummaryGroup

/-- Incremental Refresh Trade Summary Groups -/
structure IncrementalRefreshTradeSummaryGroups where
  blockLength : BitVec 16
  incrementalRefreshTradeSummaryGroup : Bounded 1 IncrementalRefreshTradeSummaryGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeSummaryGroups

def encode (message : IncrementalRefreshTradeSummaryGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshTradeSummaryGroup.val.length)
    ++ encodeMany IncrementalRefreshTradeSummaryGroup.encode message.incrementalRefreshTradeSummaryGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeSummaryGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTradeSummaryGroup_, bytes) ← decodeMany IncrementalRefreshTradeSummaryGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshTradeSummaryGroup : incrementalRefreshTradeSummaryGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshTradeSummaryGroup := ⟨incrementalRefreshTradeSummaryGroup_, fits_incrementalRefreshTradeSummaryGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshTradeSummaryGroups) : (encode message).length ≤ 8163 := by
  have bound_incrementalRefreshTradeSummaryGroup := message.incrementalRefreshTradeSummaryGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshTradeSummaryGroup.encode 32 IncrementalRefreshTradeSummaryGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshTradeSummaryGroup.encode IncrementalRefreshTradeSummaryGroup.decode IncrementalRefreshTradeSummaryGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshTradeSummaryGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshTradeSummaryGroups

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryOrderIdGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryOrderIdGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshTradeSummaryOrderIdGroup

/-- Incremental Refresh Trade Summary Order Id Groups -/
structure IncrementalRefreshTradeSummaryOrderIdGroups where
  blockLength : BitVec 16
  padding5 : Alpha 5
  incrementalRefreshTradeSummaryOrderIdGroup : Bounded 1 IncrementalRefreshTradeSummaryOrderIdGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeSummaryOrderIdGroups

def encode (message : IncrementalRefreshTradeSummaryOrderIdGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ Alpha.encode message.padding5
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshTradeSummaryOrderIdGroup.val.length)
    ++ encodeMany IncrementalRefreshTradeSummaryOrderIdGroup.encode message.incrementalRefreshTradeSummaryOrderIdGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeSummaryOrderIdGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTradeSummaryOrderIdGroup_, bytes) ← decodeMany IncrementalRefreshTradeSummaryOrderIdGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshTradeSummaryOrderIdGroup : incrementalRefreshTradeSummaryOrderIdGroup_.length < 256 ^ 1 then
    pure ({ blockLength, padding5, incrementalRefreshTradeSummaryOrderIdGroup := ⟨incrementalRefreshTradeSummaryOrderIdGroup_, fits_incrementalRefreshTradeSummaryOrderIdGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryOrderIdGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshTradeSummaryOrderIdGroups) : (encode message).length ≤ 4088 := by
  have bound_incrementalRefreshTradeSummaryOrderIdGroup := message.incrementalRefreshTradeSummaryOrderIdGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshTradeSummaryOrderIdGroup.encode 16 IncrementalRefreshTradeSummaryOrderIdGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryOrderIdGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshTradeSummaryOrderIdGroup.encode IncrementalRefreshTradeSummaryOrderIdGroup.decode IncrementalRefreshTradeSummaryOrderIdGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshTradeSummaryOrderIdGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshTradeSummaryOrderIdGroups

/-- Md Incremental Refresh Trade Summary -/
structure MdIncrementalRefreshTradeSummary where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshTradeSummaryGroups : IncrementalRefreshTradeSummaryGroups
  incrementalRefreshTradeSummaryOrderIdGroups : IncrementalRefreshTradeSummaryOrderIdGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshTradeSummary

def encode (message : MdIncrementalRefreshTradeSummary) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ IncrementalRefreshTradeSummaryGroups.encode message.incrementalRefreshTradeSummaryGroups
    ++ IncrementalRefreshTradeSummaryOrderIdGroups.encode message.incrementalRefreshTradeSummaryOrderIdGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshTradeSummary × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshTradeSummaryGroups, bytes) ← IncrementalRefreshTradeSummaryGroups.decode bytes
  let (incrementalRefreshTradeSummaryOrderIdGroups, bytes) ← IncrementalRefreshTradeSummaryOrderIdGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshTradeSummaryGroups, incrementalRefreshTradeSummaryOrderIdGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshTradeSummary) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshTradeSummary) : (encode message).length ≤ 12262 := by
  have bound_incrementalRefreshTradeSummaryGroups := IncrementalRefreshTradeSummaryGroups.encode_length_le message.incrementalRefreshTradeSummaryGroups
  have bound_incrementalRefreshTradeSummaryOrderIdGroups := IncrementalRefreshTradeSummaryOrderIdGroups.encode_length_le message.incrementalRefreshTradeSummaryOrderIdGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshTradeSummary) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshTradeSummaryGroups.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshTradeSummaryOrderIdGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryTypeDailyStatistics.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshDailyStatisticsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshDailyStatisticsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MdEntryTypeDailyStatistics.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshDailyStatisticsGroup

/-- Incremental Refresh Daily Statistics Groups -/
structure IncrementalRefreshDailyStatisticsGroups where
  blockLength : BitVec 16
  incrementalRefreshDailyStatisticsGroup : Bounded 1 IncrementalRefreshDailyStatisticsGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshDailyStatisticsGroups

def encode (message : IncrementalRefreshDailyStatisticsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshDailyStatisticsGroup.val.length)
    ++ encodeMany IncrementalRefreshDailyStatisticsGroup.encode message.incrementalRefreshDailyStatisticsGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshDailyStatisticsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshDailyStatisticsGroup_, bytes) ← decodeMany IncrementalRefreshDailyStatisticsGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshDailyStatisticsGroup : incrementalRefreshDailyStatisticsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshDailyStatisticsGroup := ⟨incrementalRefreshDailyStatisticsGroup_, fits_incrementalRefreshDailyStatisticsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshDailyStatisticsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshDailyStatisticsGroups) : (encode message).length ≤ 8163 := by
  have bound_incrementalRefreshDailyStatisticsGroup := message.incrementalRefreshDailyStatisticsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshDailyStatisticsGroup.encode 32 IncrementalRefreshDailyStatisticsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshDailyStatisticsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshDailyStatisticsGroup.encode IncrementalRefreshDailyStatisticsGroup.decode IncrementalRefreshDailyStatisticsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshDailyStatisticsGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshDailyStatisticsGroups

/-- Md Incremental Refresh Daily Statistics -/
structure MdIncrementalRefreshDailyStatistics where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshDailyStatisticsGroups : IncrementalRefreshDailyStatisticsGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshDailyStatistics

def encode (message : MdIncrementalRefreshDailyStatistics) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ IncrementalRefreshDailyStatisticsGroups.encode message.incrementalRefreshDailyStatisticsGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshDailyStatistics × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshDailyStatisticsGroups, bytes) ← IncrementalRefreshDailyStatisticsGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshDailyStatisticsGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshDailyStatistics) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshDailyStatistics) : (encode message).length ≤ 8174 := by
  have bound_incrementalRefreshDailyStatisticsGroups := IncrementalRefreshDailyStatisticsGroups.encode_length_le message.incrementalRefreshDailyStatisticsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshDailyStatistics) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshDailyStatisticsGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : IncrementalRefreshLimitsBandingGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshLimitsBandingGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end IncrementalRefreshLimitsBandingGroup

/-- Incremental Refresh Limits Banding Groups -/
structure IncrementalRefreshLimitsBandingGroups where
  blockLength : BitVec 16
  incrementalRefreshLimitsBandingGroup : Bounded 1 IncrementalRefreshLimitsBandingGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshLimitsBandingGroups

def encode (message : IncrementalRefreshLimitsBandingGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshLimitsBandingGroup.val.length)
    ++ encodeMany IncrementalRefreshLimitsBandingGroup.encode message.incrementalRefreshLimitsBandingGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshLimitsBandingGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshLimitsBandingGroup_, bytes) ← decodeMany IncrementalRefreshLimitsBandingGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshLimitsBandingGroup : incrementalRefreshLimitsBandingGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshLimitsBandingGroup := ⟨incrementalRefreshLimitsBandingGroup_, fits_incrementalRefreshLimitsBandingGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshLimitsBandingGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshLimitsBandingGroups) : (encode message).length ≤ 8163 := by
  have bound_incrementalRefreshLimitsBandingGroup := message.incrementalRefreshLimitsBandingGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshLimitsBandingGroup.encode 32 IncrementalRefreshLimitsBandingGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshLimitsBandingGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshLimitsBandingGroup.encode IncrementalRefreshLimitsBandingGroup.decode IncrementalRefreshLimitsBandingGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshLimitsBandingGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshLimitsBandingGroups

/-- Md Incremental Refresh Limits Banding -/
structure MdIncrementalRefreshLimitsBanding where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshLimitsBandingGroups : IncrementalRefreshLimitsBandingGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshLimitsBanding

def encode (message : MdIncrementalRefreshLimitsBanding) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ IncrementalRefreshLimitsBandingGroups.encode message.incrementalRefreshLimitsBandingGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshLimitsBanding × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshLimitsBandingGroups, bytes) ← IncrementalRefreshLimitsBandingGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshLimitsBandingGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshLimitsBanding) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshLimitsBanding) : (encode message).length ≤ 8174 := by
  have bound_incrementalRefreshLimitsBandingGroups := IncrementalRefreshLimitsBandingGroups.encode_length_le message.incrementalRefreshLimitsBandingGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshLimitsBanding) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshLimitsBandingGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryTypeStatistics.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshSessionStatisticsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshSessionStatisticsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MdEntryTypeStatistics.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshSessionStatisticsGroup

/-- Incremental Refresh Session Statistics Groups -/
structure IncrementalRefreshSessionStatisticsGroups where
  blockLength : BitVec 16
  incrementalRefreshSessionStatisticsGroup : Bounded 1 IncrementalRefreshSessionStatisticsGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshSessionStatisticsGroups

def encode (message : IncrementalRefreshSessionStatisticsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshSessionStatisticsGroup.val.length)
    ++ encodeMany IncrementalRefreshSessionStatisticsGroup.encode message.incrementalRefreshSessionStatisticsGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshSessionStatisticsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshSessionStatisticsGroup_, bytes) ← decodeMany IncrementalRefreshSessionStatisticsGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshSessionStatisticsGroup : incrementalRefreshSessionStatisticsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshSessionStatisticsGroup := ⟨incrementalRefreshSessionStatisticsGroup_, fits_incrementalRefreshSessionStatisticsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshSessionStatisticsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshSessionStatisticsGroups) : (encode message).length ≤ 6123 := by
  have bound_incrementalRefreshSessionStatisticsGroup := message.incrementalRefreshSessionStatisticsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshSessionStatisticsGroup.encode 24 IncrementalRefreshSessionStatisticsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshSessionStatisticsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshSessionStatisticsGroup.encode IncrementalRefreshSessionStatisticsGroup.decode IncrementalRefreshSessionStatisticsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshSessionStatisticsGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshSessionStatisticsGroups

/-- Md Incremental Refresh Session Statistics -/
structure MdIncrementalRefreshSessionStatistics where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshSessionStatisticsGroups : IncrementalRefreshSessionStatisticsGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshSessionStatistics

def encode (message : MdIncrementalRefreshSessionStatistics) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ IncrementalRefreshSessionStatisticsGroups.encode message.incrementalRefreshSessionStatisticsGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshSessionStatistics × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshSessionStatisticsGroups, bytes) ← IncrementalRefreshSessionStatisticsGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshSessionStatisticsGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshSessionStatistics) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshSessionStatistics) : (encode message).length ≤ 6134 := by
  have bound_incrementalRefreshSessionStatisticsGroups := IncrementalRefreshSessionStatisticsGroups.encode_length_le message.incrementalRefreshSessionStatisticsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshSessionStatistics) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshSessionStatisticsGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryType.encode_length]

theorem encode_length_pos (message : SnapshotFullRefreshGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotFullRefreshGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [MdEntryType.decode_encode, Option.bind_some]
  rfl

end SnapshotFullRefreshGroup

/-- Snapshot Full Refresh Groups -/
structure SnapshotFullRefreshGroups where
  blockLength : BitVec 16
  snapshotFullRefreshGroup : Bounded 1 SnapshotFullRefreshGroup
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshGroups

def encode (message : SnapshotFullRefreshGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.snapshotFullRefreshGroup.val.length)
    ++ encodeMany SnapshotFullRefreshGroup.encode message.snapshotFullRefreshGroup.val

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotFullRefreshGroup_, bytes) ← decodeMany SnapshotFullRefreshGroup.decode numInGroup.toNat bytes
  if fits_snapshotFullRefreshGroup : snapshotFullRefreshGroup_.length < 256 ^ 1 then
    pure ({ blockLength, snapshotFullRefreshGroup := ⟨snapshotFullRefreshGroup_, fits_snapshotFullRefreshGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotFullRefreshGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotFullRefreshGroups) : (encode message).length ≤ 5613 := by
  have bound_snapshotFullRefreshGroup := message.snapshotFullRefreshGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SnapshotFullRefreshGroup.encode 22 SnapshotFullRefreshGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotFullRefreshGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SnapshotFullRefreshGroup.encode SnapshotFullRefreshGroup.decode SnapshotFullRefreshGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.snapshotFullRefreshGroup.length_lt, ↓reduceDIte]
  rfl

end SnapshotFullRefreshGroups

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
  snapshotFullRefreshGroups : SnapshotFullRefreshGroups
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
    ++ SnapshotFullRefreshGroups.encode message.snapshotFullRefreshGroups

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
  let (snapshotFullRefreshGroups, bytes) ← SnapshotFullRefreshGroups.decode bytes
  pure ({ lastMsgSeqNumProcessed, totNumReports, securityId, rptSeq, transactTime, lastUpdateTime, tradeDate, mdSecurityTradingStatus, highLimitPrice, lowLimitPrice, maxPriceVariation, snapshotFullRefreshGroups }, bytes)

theorem encode_length_pos (message : SnapshotFullRefresh) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotFullRefresh) : (encode message).length ≤ 5672 := by
  have bound_snapshotFullRefreshGroups := SnapshotFullRefreshGroups.encode_length_le message.snapshotFullRefreshGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : SnapshotFullRefresh) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [SnapshotFullRefreshGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MdEntryTypeBook.encode_length]

theorem encode_length_pos (message : SnapshotFullRefreshOrderBookGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotFullRefreshOrderBookGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [MdEntryTypeBook.decode_encode, Option.bind_some]
  rfl

end SnapshotFullRefreshOrderBookGroup

/-- Snapshot Full Refresh Order Book Groups -/
structure SnapshotFullRefreshOrderBookGroups where
  blockLength : BitVec 16
  snapshotFullRefreshOrderBookGroup : Bounded 1 SnapshotFullRefreshOrderBookGroup
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshOrderBookGroups

def encode (message : SnapshotFullRefreshOrderBookGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.snapshotFullRefreshOrderBookGroup.val.length)
    ++ encodeMany SnapshotFullRefreshOrderBookGroup.encode message.snapshotFullRefreshOrderBookGroup.val

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshOrderBookGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotFullRefreshOrderBookGroup_, bytes) ← decodeMany SnapshotFullRefreshOrderBookGroup.decode numInGroup.toNat bytes
  if fits_snapshotFullRefreshOrderBookGroup : snapshotFullRefreshOrderBookGroup_.length < 256 ^ 1 then
    pure ({ blockLength, snapshotFullRefreshOrderBookGroup := ⟨snapshotFullRefreshOrderBookGroup_, fits_snapshotFullRefreshOrderBookGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotFullRefreshOrderBookGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotFullRefreshOrderBookGroups) : (encode message).length ≤ 7398 := by
  have bound_snapshotFullRefreshOrderBookGroup := message.snapshotFullRefreshOrderBookGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SnapshotFullRefreshOrderBookGroup.encode 29 SnapshotFullRefreshOrderBookGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotFullRefreshOrderBookGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SnapshotFullRefreshOrderBookGroup.encode SnapshotFullRefreshOrderBookGroup.decode SnapshotFullRefreshOrderBookGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.snapshotFullRefreshOrderBookGroup.length_lt, ↓reduceDIte]
  rfl

end SnapshotFullRefreshOrderBookGroups

/-- Snapshot Full Refresh Order Book -/
structure SnapshotFullRefreshOrderBook where
  lastMsgSeqNumProcessed : BitVec 32
  totNumReports : BitVec 32
  securityId : BitVec 32
  noChunks : BitVec 32
  currentChunk : BitVec 32
  transactTime : BitVec 64
  snapshotFullRefreshOrderBookGroups : SnapshotFullRefreshOrderBookGroups
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshOrderBook

def encode (message : SnapshotFullRefreshOrderBook) : List UInt8 :=
  encodeUIntLE 4 message.lastMsgSeqNumProcessed
    ++ encodeUIntLE 4 message.totNumReports
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.noChunks
    ++ encodeUIntLE 4 message.currentChunk
    ++ encodeUIntLE 8 message.transactTime
    ++ SnapshotFullRefreshOrderBookGroups.encode message.snapshotFullRefreshOrderBookGroups

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshOrderBook × List UInt8) := do
  let (lastMsgSeqNumProcessed, bytes) ← decodeUIntLE 4 bytes
  let (totNumReports, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (noChunks, bytes) ← decodeUIntLE 4 bytes
  let (currentChunk, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (snapshotFullRefreshOrderBookGroups, bytes) ← SnapshotFullRefreshOrderBookGroups.decode bytes
  pure ({ lastMsgSeqNumProcessed, totNumReports, securityId, noChunks, currentChunk, transactTime, snapshotFullRefreshOrderBookGroups }, bytes)

theorem encode_length_pos (message : SnapshotFullRefreshOrderBook) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotFullRefreshOrderBook) : (encode message).length ≤ 7426 := by
  have bound_snapshotFullRefreshOrderBookGroups := SnapshotFullRefreshOrderBookGroups.encode_length_le message.snapshotFullRefreshOrderBookGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : SnapshotFullRefreshOrderBook) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [SnapshotFullRefreshOrderBookGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MaturityMonthYear) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaturityMonthYear) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : EventsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EventsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end EventsGroup

/-- Events Groups -/
structure EventsGroups where
  blockLength : BitVec 16
  eventsGroup : Bounded 1 EventsGroup
  deriving DecidableEq, Repr

namespace EventsGroups

def encode (message : EventsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.eventsGroup.val.length)
    ++ encodeMany EventsGroup.encode message.eventsGroup.val

def decode (bytes : List UInt8) : Option (EventsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (eventsGroup_, bytes) ← decodeMany EventsGroup.decode numInGroup.toNat bytes
  if fits_eventsGroup : eventsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, eventsGroup := ⟨eventsGroup_, fits_eventsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : EventsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EventsGroups) : (encode message).length ≤ 2298 := by
  have bound_eventsGroup := message.eventsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const EventsGroup.encode 9 EventsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : EventsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 EventsGroup.encode EventsGroup.decode EventsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.eventsGroup.length_lt, ↓reduceDIte]
  rfl

end EventsGroups

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
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FeedTypesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FeedTypesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end FeedTypesGroup

/-- Feed Types Groups -/
structure FeedTypesGroups where
  blockLength : BitVec 16
  feedTypesGroup : Bounded 1 FeedTypesGroup
  deriving DecidableEq, Repr

namespace FeedTypesGroups

def encode (message : FeedTypesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.feedTypesGroup.val.length)
    ++ encodeMany FeedTypesGroup.encode message.feedTypesGroup.val

def decode (bytes : List UInt8) : Option (FeedTypesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (feedTypesGroup_, bytes) ← decodeMany FeedTypesGroup.decode numInGroup.toNat bytes
  if fits_feedTypesGroup : feedTypesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, feedTypesGroup := ⟨feedTypesGroup_, fits_feedTypesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : FeedTypesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FeedTypesGroups) : (encode message).length ≤ 1023 := by
  have bound_feedTypesGroup := message.feedTypesGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const FeedTypesGroup.encode 4 FeedTypesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : FeedTypesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 FeedTypesGroup.encode FeedTypesGroup.decode FeedTypesGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.feedTypesGroup.length_lt, ↓reduceDIte]
  rfl

end FeedTypesGroups

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
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : InstAttribGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstAttribGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end InstAttribGroup

/-- Inst Attrib Groups -/
structure InstAttribGroups where
  blockLength : BitVec 16
  instAttribGroup : Bounded 1 InstAttribGroup
  deriving DecidableEq, Repr

namespace InstAttribGroups

def encode (message : InstAttribGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.instAttribGroup.val.length)
    ++ encodeMany InstAttribGroup.encode message.instAttribGroup.val

def decode (bytes : List UInt8) : Option (InstAttribGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (instAttribGroup_, bytes) ← decodeMany InstAttribGroup.decode numInGroup.toNat bytes
  if fits_instAttribGroup : instAttribGroup_.length < 256 ^ 1 then
    pure ({ blockLength, instAttribGroup := ⟨instAttribGroup_, fits_instAttribGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : InstAttribGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InstAttribGroups) : (encode message).length ≤ 1023 := by
  have bound_instAttribGroup := message.instAttribGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const InstAttribGroup.encode 4 InstAttribGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : InstAttribGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 InstAttribGroup.encode InstAttribGroup.decode InstAttribGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.instAttribGroup.length_lt, ↓reduceDIte]
  rfl

end InstAttribGroups

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
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LotTypeRulesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LotTypeRulesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end LotTypeRulesGroup

/-- Lot Type Rules Groups -/
structure LotTypeRulesGroups where
  blockLength : BitVec 16
  lotTypeRulesGroup : Bounded 1 LotTypeRulesGroup
  deriving DecidableEq, Repr

namespace LotTypeRulesGroups

def encode (message : LotTypeRulesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.lotTypeRulesGroup.val.length)
    ++ encodeMany LotTypeRulesGroup.encode message.lotTypeRulesGroup.val

def decode (bytes : List UInt8) : Option (LotTypeRulesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (lotTypeRulesGroup_, bytes) ← decodeMany LotTypeRulesGroup.decode numInGroup.toNat bytes
  if fits_lotTypeRulesGroup : lotTypeRulesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, lotTypeRulesGroup := ⟨lotTypeRulesGroup_, fits_lotTypeRulesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LotTypeRulesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LotTypeRulesGroups) : (encode message).length ≤ 1278 := by
  have bound_lotTypeRulesGroup := message.lotTypeRulesGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const LotTypeRulesGroup.encode 5 LotTypeRulesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LotTypeRulesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 LotTypeRulesGroup.encode LotTypeRulesGroup.decode LotTypeRulesGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.lotTypeRulesGroup.length_lt, ↓reduceDIte]
  rfl

end LotTypeRulesGroups

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
  eventsGroups : EventsGroups
  feedTypesGroups : FeedTypesGroups
  instAttribGroups : InstAttribGroups
  lotTypeRulesGroups : LotTypeRulesGroups
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
    ++ EventsGroups.encode message.eventsGroups
    ++ FeedTypesGroups.encode message.feedTypesGroups
    ++ InstAttribGroups.encode message.instAttribGroups
    ++ LotTypeRulesGroups.encode message.lotTypeRulesGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
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
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  let (feedTypesGroups, bytes) ← FeedTypesGroups.decode bytes
  let (instAttribGroups, bytes) ← InstAttribGroups.decode bytes
  let (lotTypeRulesGroups, bytes) ← LotTypeRulesGroups.decode bytes
  pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, maturityMonthYear, currency, settlCurrency, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementEx, displayFactor, mainFraction, subFraction, priceDisplayFormat, unitOfMeasure, unitOfMeasureQty, tradingReferencePrice, settlPriceType, openInterestQty, clearedVolume, highLimitPrice, lowLimitPrice, maxPriceVariation, decayQuantity, decayStartDate, originalContractSize, contractMultiplier, contractMultiplierUnit, flowScheduleType, minPriceIncrementAmount, userDefinedInstrument, tradingReferenceDate, instrumentGuid, eventsGroups, feedTypesGroups, instAttribGroups, lotTypeRulesGroups }, bytes)

theorem encode_length_pos (message : MdInstrumentDefinitionFuture) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdInstrumentDefinitionFuture) : (encode message).length ≤ 5846 := by
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  have bound_feedTypesGroups := FeedTypesGroups.encode_length_le message.feedTypesGroups
  have bound_instAttribGroups := InstAttribGroups.encode_length_le message.instAttribGroups
  have bound_lotTypeRulesGroups := LotTypeRulesGroups.encode_length_le message.lotTypeRulesGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityUpdateAction.encode_length, encodeUInt_length, Alpha.encode_length, MaturityMonthYear.encode_length]
  omega

@[simp] theorem decode_encode (message : MdInstrumentDefinitionFuture) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [SecurityUpdateAction.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [MaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [EventsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [FeedTypesGroups.decode_encode]
  simp only [Option.bind_some]
  rw [InstAttribGroups.decode_encode]
  simp only [Option.bind_some]
  rw [LotTypeRulesGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OptionUnderlyingsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionUnderlyingsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OptionUnderlyingsGroup

/-- Option Underlyings Groups -/
structure OptionUnderlyingsGroups where
  blockLength : BitVec 16
  optionUnderlyingsGroup : Bounded 1 OptionUnderlyingsGroup
  deriving DecidableEq, Repr

namespace OptionUnderlyingsGroups

def encode (message : OptionUnderlyingsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.optionUnderlyingsGroup.val.length)
    ++ encodeMany OptionUnderlyingsGroup.encode message.optionUnderlyingsGroup.val

def decode (bytes : List UInt8) : Option (OptionUnderlyingsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (optionUnderlyingsGroup_, bytes) ← decodeMany OptionUnderlyingsGroup.decode numInGroup.toNat bytes
  if fits_optionUnderlyingsGroup : optionUnderlyingsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, optionUnderlyingsGroup := ⟨optionUnderlyingsGroup_, fits_optionUnderlyingsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OptionUnderlyingsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OptionUnderlyingsGroups) : (encode message).length ≤ 6123 := by
  have bound_optionUnderlyingsGroup := message.optionUnderlyingsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const OptionUnderlyingsGroup.encode 24 OptionUnderlyingsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OptionUnderlyingsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OptionUnderlyingsGroup.encode OptionUnderlyingsGroup.decode OptionUnderlyingsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.optionUnderlyingsGroup.length_lt, ↓reduceDIte]
  rfl

end OptionUnderlyingsGroups

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OptionRelatedInstrumentsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionRelatedInstrumentsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OptionRelatedInstrumentsGroup

/-- Option Related Instruments Groups -/
structure OptionRelatedInstrumentsGroups where
  blockLength : BitVec 16
  optionRelatedInstrumentsGroup : Bounded 1 OptionRelatedInstrumentsGroup
  deriving DecidableEq, Repr

namespace OptionRelatedInstrumentsGroups

def encode (message : OptionRelatedInstrumentsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.optionRelatedInstrumentsGroup.val.length)
    ++ encodeMany OptionRelatedInstrumentsGroup.encode message.optionRelatedInstrumentsGroup.val

def decode (bytes : List UInt8) : Option (OptionRelatedInstrumentsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (optionRelatedInstrumentsGroup_, bytes) ← decodeMany OptionRelatedInstrumentsGroup.decode numInGroup.toNat bytes
  if fits_optionRelatedInstrumentsGroup : optionRelatedInstrumentsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, optionRelatedInstrumentsGroup := ⟨optionRelatedInstrumentsGroup_, fits_optionRelatedInstrumentsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OptionRelatedInstrumentsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OptionRelatedInstrumentsGroups) : (encode message).length ≤ 6123 := by
  have bound_optionRelatedInstrumentsGroup := message.optionRelatedInstrumentsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const OptionRelatedInstrumentsGroup.encode 24 OptionRelatedInstrumentsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OptionRelatedInstrumentsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OptionRelatedInstrumentsGroup.encode OptionRelatedInstrumentsGroup.decode OptionRelatedInstrumentsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.optionRelatedInstrumentsGroup.length_lt, ↓reduceDIte]
  rfl

end OptionRelatedInstrumentsGroups

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
  eventsGroups : EventsGroups
  feedTypesGroups : FeedTypesGroups
  instAttribGroups : InstAttribGroups
  lotTypeRulesGroups : LotTypeRulesGroups
  optionUnderlyingsGroups : OptionUnderlyingsGroups
  optionRelatedInstrumentsGroups : OptionRelatedInstrumentsGroups
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
    ++ EventsGroups.encode message.eventsGroups
    ++ FeedTypesGroups.encode message.feedTypesGroups
    ++ InstAttribGroups.encode message.instAttribGroups
    ++ LotTypeRulesGroups.encode message.lotTypeRulesGroups
    ++ OptionUnderlyingsGroups.encode message.optionUnderlyingsGroups
    ++ OptionRelatedInstrumentsGroups.encode message.optionRelatedInstrumentsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
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
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  let (feedTypesGroups, bytes) ← FeedTypesGroups.decode bytes
  let (instAttribGroups, bytes) ← InstAttribGroups.decode bytes
  let (lotTypeRulesGroups, bytes) ← LotTypeRulesGroups.decode bytes
  let (optionUnderlyingsGroups, bytes) ← OptionUnderlyingsGroups.decode bytes
  let (optionRelatedInstrumentsGroups, bytes) ← OptionRelatedInstrumentsGroups.decode bytes
  pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, putOrCall, maturityMonthYear, currency, strikePrice, strikeCurrency, settlCurrency, minCabPrice, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementOptionalEx, minPriceIncrementAmount, displayFactor, tickRule, mainFraction, subFraction, priceDisplayFormat, unitOfMeasure, unitOfMeasureQty, tradingReferencePrice, settlPriceType, clearedVolume, openInterestQty, lowLimitPrice, highLimitPrice, userDefinedInstrument, tradingReferenceDate, instrumentGuid, eventsGroups, feedTypesGroups, instAttribGroups, lotTypeRulesGroups, optionUnderlyingsGroups, optionRelatedInstrumentsGroups }, bytes)

theorem encode_length_pos (message : MdInstrumentDefinitionOption) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdInstrumentDefinitionOption) : (encode message).length ≤ 18089 := by
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  have bound_feedTypesGroups := FeedTypesGroups.encode_length_le message.feedTypesGroups
  have bound_instAttribGroups := InstAttribGroups.encode_length_le message.instAttribGroups
  have bound_lotTypeRulesGroups := LotTypeRulesGroups.encode_length_le message.lotTypeRulesGroups
  have bound_optionUnderlyingsGroups := OptionUnderlyingsGroups.encode_length_le message.optionUnderlyingsGroups
  have bound_optionRelatedInstrumentsGroups := OptionRelatedInstrumentsGroups.encode_length_le message.optionRelatedInstrumentsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityUpdateAction.encode_length, encodeUInt_length, Alpha.encode_length, MaturityMonthYear.encode_length]
  omega

@[simp] theorem decode_encode (message : MdInstrumentDefinitionOption) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [SecurityUpdateAction.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [EventsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [FeedTypesGroups.decode_encode]
  simp only [Option.bind_some]
  rw [InstAttribGroups.decode_encode]
  simp only [Option.bind_some]
  rw [LotTypeRulesGroups.decode_encode]
  simp only [Option.bind_some]
  rw [OptionUnderlyingsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [OptionRelatedInstrumentsGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end LegsGroup

/-- Legs Groups -/
structure LegsGroups where
  blockLength : BitVec 16
  legsGroup : Bounded 1 LegsGroup
  deriving DecidableEq, Repr

namespace LegsGroups

def encode (message : LegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.legsGroup.val.length)
    ++ encodeMany LegsGroup.encode message.legsGroup.val

def decode (bytes : List UInt8) : Option (LegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (legsGroup_, bytes) ← decodeMany LegsGroup.decode numInGroup.toNat bytes
  if fits_legsGroup : legsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, legsGroup := ⟨legsGroup_, fits_legsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LegsGroups) : (encode message).length ≤ 4593 := by
  have bound_legsGroup := message.legsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const LegsGroup.encode 18 LegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 LegsGroup.encode LegsGroup.decode LegsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.legsGroup.length_lt, ↓reduceDIte]
  rfl

end LegsGroups

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
  eventsGroups : EventsGroups
  feedTypesGroups : FeedTypesGroups
  instAttribGroups : InstAttribGroups
  lotTypeRulesGroups : LotTypeRulesGroups
  legsGroups : LegsGroups
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
    ++ EventsGroups.encode message.eventsGroups
    ++ FeedTypesGroups.encode message.feedTypesGroups
    ++ InstAttribGroups.encode message.instAttribGroups
    ++ LotTypeRulesGroups.encode message.lotTypeRulesGroups
    ++ LegsGroups.encode message.legsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
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
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  let (feedTypesGroups, bytes) ← FeedTypesGroups.decode bytes
  let (instAttribGroups, bytes) ← InstAttribGroups.decode bytes
  let (lotTypeRulesGroups, bytes) ← LotTypeRulesGroups.decode bytes
  let (legsGroups, bytes) ← LegsGroups.decode bytes
  pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProductOptional, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, maturityMonthYear, currency, securitySubType, userDefinedInstrument, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementOptionalEx, displayFactor, priceDisplayFormat, priceRatio, tickRule, unitOfMeasure, tradingReferencePrice, settlPriceType, openInterestQty, clearedVolume, highLimitPrice, lowLimitPrice, maxPriceVariation, mainFraction, subFraction, tradingReferenceDate, priceQuoteMethod, riskSet, marketSet, instrumentGuid, financialInstrumentFullName, eventsGroups, feedTypesGroups, instAttribGroups, lotTypeRulesGroups, legsGroups }, bytes)

theorem encode_length_pos (message : MdInstrumentDefinitionSpread) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdInstrumentDefinitionSpread) : (encode message).length ≤ 10470 := by
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  have bound_feedTypesGroups := FeedTypesGroups.encode_length_le message.feedTypesGroups
  have bound_instAttribGroups := InstAttribGroups.encode_length_le message.instAttribGroups
  have bound_lotTypeRulesGroups := LotTypeRulesGroups.encode_length_le message.lotTypeRulesGroups
  have bound_legsGroups := LegsGroups.encode_length_le message.legsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityUpdateAction.encode_length, encodeUInt_length, Alpha.encode_length, MaturityMonthYear.encode_length]
  omega

@[simp] theorem decode_encode (message : MdInstrumentDefinitionSpread) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [SecurityUpdateAction.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [MaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [EventsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [FeedTypesGroups.decode_encode]
  simp only [Option.bind_some]
  rw [InstAttribGroups.decode_encode]
  simp only [Option.bind_some]
  rw [LotTypeRulesGroups.decode_encode]
  simp only [Option.bind_some]
  rw [LegsGroups.decode_encode, Option.bind_some]
  rfl

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
  eventsGroups : EventsGroups
  feedTypesGroups : FeedTypesGroups
  instAttribGroups : InstAttribGroups
  lotTypeRulesGroups : LotTypeRulesGroups
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
    ++ EventsGroups.encode message.eventsGroups
    ++ FeedTypesGroups.encode message.feedTypesGroups
    ++ InstAttribGroups.encode message.instAttribGroups
    ++ LotTypeRulesGroups.encode message.lotTypeRulesGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
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
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  let (feedTypesGroups, bytes) ← FeedTypesGroups.decode bytes
  let (instAttribGroups, bytes) ← InstAttribGroups.decode bytes
  let (lotTypeRulesGroups, bytes) ← LotTypeRulesGroups.decode bytes
  pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, currency, settlCurrency, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementOptionalEx, displayFactor, mainFraction, subFraction, priceDisplayFormat, unitOfMeasure, unitOfMeasureQty, tradingReferencePrice, tradingReferenceDate, highLimitPrice, lowLimitPrice, maxPriceVariation, minPriceIncrementAmount, issueDate, datedDate, maturityDate, couponRate, parValue, couponFrequencyUnit, couponFrequencyPeriod, couponDayCount, countryOfIssue, issuer, financialInstrumentFullName, securityAltId, securityAltIdSource, priceQuoteMethod, partyRoleClearingOrg, userDefinedInstrument, riskSet, marketSet, instrumentGuid, eventsGroups, feedTypesGroups, instAttribGroups, lotTypeRulesGroups }, bytes)

theorem encode_length_pos (message : MdInstrumentDefinitionFixedIncome) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdInstrumentDefinitionFixedIncome) : (encode message).length ≤ 5960 := by
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  have bound_feedTypesGroups := FeedTypesGroups.encode_length_le message.feedTypesGroups
  have bound_instAttribGroups := InstAttribGroups.encode_length_le message.instAttribGroups
  have bound_lotTypeRulesGroups := LotTypeRulesGroups.encode_length_le message.lotTypeRulesGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityUpdateAction.encode_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdInstrumentDefinitionFixedIncome) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [SecurityUpdateAction.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [EventsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [FeedTypesGroups.decode_encode]
  simp only [Option.bind_some]
  rw [InstAttribGroups.decode_encode]
  simp only [Option.bind_some]
  rw [LotTypeRulesGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RepoUnderlyingsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RepoUnderlyingsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end RepoUnderlyingsGroup

/-- Repo Underlyings Groups -/
structure RepoUnderlyingsGroups where
  blockLength : BitVec 16
  repoUnderlyingsGroup : Bounded 1 RepoUnderlyingsGroup
  deriving DecidableEq, Repr

namespace RepoUnderlyingsGroups

def encode (message : RepoUnderlyingsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.repoUnderlyingsGroup.val.length)
    ++ encodeMany RepoUnderlyingsGroup.encode message.repoUnderlyingsGroup.val

def decode (bytes : List UInt8) : Option (RepoUnderlyingsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (repoUnderlyingsGroup_, bytes) ← decodeMany RepoUnderlyingsGroup.decode numInGroup.toNat bytes
  if fits_repoUnderlyingsGroup : repoUnderlyingsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, repoUnderlyingsGroup := ⟨repoUnderlyingsGroup_, fits_repoUnderlyingsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : RepoUnderlyingsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RepoUnderlyingsGroups) : (encode message).length ≤ 30093 := by
  have bound_repoUnderlyingsGroup := message.repoUnderlyingsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const RepoUnderlyingsGroup.encode 118 RepoUnderlyingsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : RepoUnderlyingsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 RepoUnderlyingsGroup.encode RepoUnderlyingsGroup.decode RepoUnderlyingsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.repoUnderlyingsGroup.length_lt, ↓reduceDIte]
  rfl

end RepoUnderlyingsGroups

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RepoRelatedInstrumentsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RepoRelatedInstrumentsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end RepoRelatedInstrumentsGroup

/-- Repo Related Instruments Groups -/
structure RepoRelatedInstrumentsGroups where
  blockLength : BitVec 16
  repoRelatedInstrumentsGroup : Bounded 1 RepoRelatedInstrumentsGroup
  deriving DecidableEq, Repr

namespace RepoRelatedInstrumentsGroups

def encode (message : RepoRelatedInstrumentsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.repoRelatedInstrumentsGroup.val.length)
    ++ encodeMany RepoRelatedInstrumentsGroup.encode message.repoRelatedInstrumentsGroup.val

def decode (bytes : List UInt8) : Option (RepoRelatedInstrumentsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (repoRelatedInstrumentsGroup_, bytes) ← decodeMany RepoRelatedInstrumentsGroup.decode numInGroup.toNat bytes
  if fits_repoRelatedInstrumentsGroup : repoRelatedInstrumentsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, repoRelatedInstrumentsGroup := ⟨repoRelatedInstrumentsGroup_, fits_repoRelatedInstrumentsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : RepoRelatedInstrumentsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RepoRelatedInstrumentsGroups) : (encode message).length ≤ 8163 := by
  have bound_repoRelatedInstrumentsGroup := message.repoRelatedInstrumentsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const RepoRelatedInstrumentsGroup.encode 32 RepoRelatedInstrumentsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : RepoRelatedInstrumentsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 RepoRelatedInstrumentsGroup.encode RepoRelatedInstrumentsGroup.decode RepoRelatedInstrumentsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.repoRelatedInstrumentsGroup.length_lt, ↓reduceDIte]
  rfl

end RepoRelatedInstrumentsGroups

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
  eventsGroups : EventsGroups
  feedTypesGroups : FeedTypesGroups
  instAttribGroups : InstAttribGroups
  lotTypeRulesGroups : LotTypeRulesGroups
  repoUnderlyingsGroups : RepoUnderlyingsGroups
  repoRelatedInstrumentsGroups : RepoRelatedInstrumentsGroups
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
    ++ EventsGroups.encode message.eventsGroups
    ++ FeedTypesGroups.encode message.feedTypesGroups
    ++ InstAttribGroups.encode message.instAttribGroups
    ++ LotTypeRulesGroups.encode message.lotTypeRulesGroups
    ++ RepoUnderlyingsGroups.encode message.repoUnderlyingsGroups
    ++ RepoRelatedInstrumentsGroups.encode message.repoRelatedInstrumentsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
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
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  let (feedTypesGroups, bytes) ← FeedTypesGroups.decode bytes
  let (instAttribGroups, bytes) ← InstAttribGroups.decode bytes
  let (lotTypeRulesGroups, bytes) ← LotTypeRulesGroups.decode bytes
  let (repoUnderlyingsGroups, bytes) ← RepoUnderlyingsGroups.decode bytes
  let (repoRelatedInstrumentsGroups, bytes) ← RepoRelatedInstrumentsGroups.decode bytes
  pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, currency, settlCurrency, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementEx, displayFactor, unitOfMeasure, unitOfMeasureQty, tradingReferencePrice, tradingReferenceDate, highLimitPrice, lowLimitPrice, maxPriceVariation, financialInstrumentFullName, partyRoleClearingOrg, startDate, endDate, terminationType, repoSubType, moneyOrPar, maxNoOfSubstitutions, priceQuoteMethod, userDefinedInstrument, riskSet, marketSet, instrumentGuid, termCode, eventsGroups, feedTypesGroups, instAttribGroups, lotTypeRulesGroups, repoUnderlyingsGroups, repoRelatedInstrumentsGroups }, bytes)

theorem encode_length_pos (message : MdInstrumentDefinitionRepo) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdInstrumentDefinitionRepo) : (encode message).length ≤ 44153 := by
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  have bound_feedTypesGroups := FeedTypesGroups.encode_length_le message.feedTypesGroups
  have bound_instAttribGroups := InstAttribGroups.encode_length_le message.instAttribGroups
  have bound_lotTypeRulesGroups := LotTypeRulesGroups.encode_length_le message.lotTypeRulesGroups
  have bound_repoUnderlyingsGroups := RepoUnderlyingsGroups.encode_length_le message.repoUnderlyingsGroups
  have bound_repoRelatedInstrumentsGroups := RepoRelatedInstrumentsGroups.encode_length_le message.repoRelatedInstrumentsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityUpdateAction.encode_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdInstrumentDefinitionRepo) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [SecurityUpdateAction.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [EventsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [FeedTypesGroups.decode_encode]
  simp only [Option.bind_some]
  rw [InstAttribGroups.decode_encode]
  simp only [Option.bind_some]
  rw [LotTypeRulesGroups.decode_encode]
  simp only [Option.bind_some]
  rw [RepoUnderlyingsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [RepoRelatedInstrumentsGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MdEntryTypeBook.encode_length]

theorem encode_length_pos (message : SnapshotRefreshTopOrdersGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotRefreshTopOrdersGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [MdEntryTypeBook.decode_encode, Option.bind_some]
  rfl

end SnapshotRefreshTopOrdersGroup

/-- Snapshot Refresh Top Orders Groups -/
structure SnapshotRefreshTopOrdersGroups where
  blockLength : BitVec 16
  snapshotRefreshTopOrdersGroup : Bounded 1 SnapshotRefreshTopOrdersGroup
  deriving DecidableEq, Repr

namespace SnapshotRefreshTopOrdersGroups

def encode (message : SnapshotRefreshTopOrdersGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.snapshotRefreshTopOrdersGroup.val.length)
    ++ encodeMany SnapshotRefreshTopOrdersGroup.encode message.snapshotRefreshTopOrdersGroup.val

def decode (bytes : List UInt8) : Option (SnapshotRefreshTopOrdersGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotRefreshTopOrdersGroup_, bytes) ← decodeMany SnapshotRefreshTopOrdersGroup.decode numInGroup.toNat bytes
  if fits_snapshotRefreshTopOrdersGroup : snapshotRefreshTopOrdersGroup_.length < 256 ^ 1 then
    pure ({ blockLength, snapshotRefreshTopOrdersGroup := ⟨snapshotRefreshTopOrdersGroup_, fits_snapshotRefreshTopOrdersGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotRefreshTopOrdersGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotRefreshTopOrdersGroups) : (encode message).length ≤ 7398 := by
  have bound_snapshotRefreshTopOrdersGroup := message.snapshotRefreshTopOrdersGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SnapshotRefreshTopOrdersGroup.encode 29 SnapshotRefreshTopOrdersGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotRefreshTopOrdersGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SnapshotRefreshTopOrdersGroup.encode SnapshotRefreshTopOrdersGroup.decode SnapshotRefreshTopOrdersGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.snapshotRefreshTopOrdersGroup.length_lt, ↓reduceDIte]
  rfl

end SnapshotRefreshTopOrdersGroups

/-- Snapshot Refresh Top Orders -/
structure SnapshotRefreshTopOrders where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  securityId : BitVec 32
  snapshotRefreshTopOrdersGroups : SnapshotRefreshTopOrdersGroups
  deriving DecidableEq, Repr

namespace SnapshotRefreshTopOrders

def encode (message : SnapshotRefreshTopOrders) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 4 message.securityId
    ++ SnapshotRefreshTopOrdersGroups.encode message.snapshotRefreshTopOrdersGroups

def decode (bytes : List UInt8) : Option (SnapshotRefreshTopOrders × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (snapshotRefreshTopOrdersGroups, bytes) ← SnapshotRefreshTopOrdersGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, securityId, snapshotRefreshTopOrdersGroups }, bytes)

theorem encode_length_pos (message : SnapshotRefreshTopOrders) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotRefreshTopOrders) : (encode message).length ≤ 7411 := by
  have bound_snapshotRefreshTopOrdersGroups := SnapshotRefreshTopOrdersGroups.encode_length_le message.snapshotRefreshTopOrdersGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : SnapshotRefreshTopOrders) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [SnapshotRefreshTopOrdersGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityStatusWorkupGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusWorkupGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end SecurityStatusWorkupGroup

/-- Security Status Workup Groups -/
structure SecurityStatusWorkupGroups where
  blockLength : BitVec 16
  securityStatusWorkupGroup : Bounded 1 SecurityStatusWorkupGroup
  deriving DecidableEq, Repr

namespace SecurityStatusWorkupGroups

def encode (message : SecurityStatusWorkupGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityStatusWorkupGroup.val.length)
    ++ encodeMany SecurityStatusWorkupGroup.encode message.securityStatusWorkupGroup.val

def decode (bytes : List UInt8) : Option (SecurityStatusWorkupGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityStatusWorkupGroup_, bytes) ← decodeMany SecurityStatusWorkupGroup.decode numInGroup.toNat bytes
  if fits_securityStatusWorkupGroup : securityStatusWorkupGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityStatusWorkupGroup := ⟨securityStatusWorkupGroup_, fits_securityStatusWorkupGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityStatusWorkupGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityStatusWorkupGroups) : (encode message).length ≤ 2553 := by
  have bound_securityStatusWorkupGroup := message.securityStatusWorkupGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityStatusWorkupGroup.encode 10 SecurityStatusWorkupGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityStatusWorkupGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SecurityStatusWorkupGroup.encode SecurityStatusWorkupGroup.decode SecurityStatusWorkupGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.securityStatusWorkupGroup.length_lt, ↓reduceDIte]
  rfl

end SecurityStatusWorkupGroups

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
  securityStatusWorkupGroups : SecurityStatusWorkupGroups
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
    ++ SecurityStatusWorkupGroups.encode message.securityStatusWorkupGroups

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
  let (securityStatusWorkupGroups, bytes) ← SecurityStatusWorkupGroups.decode bytes
  pure ({ transactTime, mdEntryPxOptionalEx, securityId, matchEventIndicator, tradeDate, tradeLinkId, workupTradingStatus, haltReason, securityTradingEvent, securityStatusWorkupGroups }, bytes)

theorem encode_length_pos (message : SecurityStatusWorkup) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityStatusWorkup) : (encode message).length ≤ 2583 := by
  have bound_securityStatusWorkupGroups := SecurityStatusWorkupGroups.encode_length_le message.securityStatusWorkupGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : SecurityStatusWorkup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [SecurityStatusWorkupGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryType.encode_length]

theorem encode_length_pos (message : SnapshotFullRefreshTcpGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotFullRefreshTcpGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MdEntryType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end SnapshotFullRefreshTcpGroup

/-- Snapshot Full Refresh Tcp Groups -/
structure SnapshotFullRefreshTcpGroups where
  blockLength : BitVec 16
  snapshotFullRefreshTcpGroup : Bounded 1 SnapshotFullRefreshTcpGroup
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshTcpGroups

def encode (message : SnapshotFullRefreshTcpGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.snapshotFullRefreshTcpGroup.val.length)
    ++ encodeMany SnapshotFullRefreshTcpGroup.encode message.snapshotFullRefreshTcpGroup.val

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshTcpGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotFullRefreshTcpGroup_, bytes) ← decodeMany SnapshotFullRefreshTcpGroup.decode numInGroup.toNat bytes
  if fits_snapshotFullRefreshTcpGroup : snapshotFullRefreshTcpGroup_.length < 256 ^ 1 then
    pure ({ blockLength, snapshotFullRefreshTcpGroup := ⟨snapshotFullRefreshTcpGroup_, fits_snapshotFullRefreshTcpGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotFullRefreshTcpGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotFullRefreshTcpGroups) : (encode message).length ≤ 6633 := by
  have bound_snapshotFullRefreshTcpGroup := message.snapshotFullRefreshTcpGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SnapshotFullRefreshTcpGroup.encode 26 SnapshotFullRefreshTcpGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotFullRefreshTcpGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SnapshotFullRefreshTcpGroup.encode SnapshotFullRefreshTcpGroup.decode SnapshotFullRefreshTcpGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.snapshotFullRefreshTcpGroup.length_lt, ↓reduceDIte]
  rfl

end SnapshotFullRefreshTcpGroups

/-- Snapshot Full Refresh Tcp -/
structure SnapshotFullRefreshTcp where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  securityId : BitVec 32
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  snapshotFullRefreshTcpGroups : SnapshotFullRefreshTcpGroups
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshTcp

def encode (message : SnapshotFullRefreshTcp) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 8 message.highLimitPrice
    ++ encodeUIntLE 8 message.lowLimitPrice
    ++ encodeUIntLE 8 message.maxPriceVariation
    ++ SnapshotFullRefreshTcpGroups.encode message.snapshotFullRefreshTcpGroups

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshTcp × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (snapshotFullRefreshTcpGroups, bytes) ← SnapshotFullRefreshTcpGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, securityId, highLimitPrice, lowLimitPrice, maxPriceVariation, snapshotFullRefreshTcpGroups }, bytes)

theorem encode_length_pos (message : SnapshotFullRefreshTcp) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotFullRefreshTcp) : (encode message).length ≤ 6670 := by
  have bound_snapshotFullRefreshTcpGroups := SnapshotFullRefreshTcpGroups.encode_length_le message.snapshotFullRefreshTcpGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : SnapshotFullRefreshTcp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [SnapshotFullRefreshTcpGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : CollateralMarketValueGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CollateralMarketValueGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end CollateralMarketValueGroup

/-- Collateral Market Value Groups -/
structure CollateralMarketValueGroups where
  blockLength : BitVec 16
  collateralMarketValueGroup : Bounded 1 CollateralMarketValueGroup
  deriving DecidableEq, Repr

namespace CollateralMarketValueGroups

def encode (message : CollateralMarketValueGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.collateralMarketValueGroup.val.length)
    ++ encodeMany CollateralMarketValueGroup.encode message.collateralMarketValueGroup.val

def decode (bytes : List UInt8) : Option (CollateralMarketValueGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (collateralMarketValueGroup_, bytes) ← decodeMany CollateralMarketValueGroup.decode numInGroup.toNat bytes
  if fits_collateralMarketValueGroup : collateralMarketValueGroup_.length < 256 ^ 1 then
    pure ({ blockLength, collateralMarketValueGroup := ⟨collateralMarketValueGroup_, fits_collateralMarketValueGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : CollateralMarketValueGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : CollateralMarketValueGroups) : (encode message).length ≤ 10203 := by
  have bound_collateralMarketValueGroup := message.collateralMarketValueGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const CollateralMarketValueGroup.encode 40 CollateralMarketValueGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : CollateralMarketValueGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 CollateralMarketValueGroup.encode CollateralMarketValueGroup.decode CollateralMarketValueGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.collateralMarketValueGroup.length_lt, ↓reduceDIte]
  rfl

end CollateralMarketValueGroups

/-- Collateral Market Value -/
structure CollateralMarketValue where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  collateralMarketValueGroups : CollateralMarketValueGroups
  deriving DecidableEq, Repr

namespace CollateralMarketValue

def encode (message : CollateralMarketValue) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ CollateralMarketValueGroups.encode message.collateralMarketValueGroups

def decode (bytes : List UInt8) : Option (CollateralMarketValue × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (collateralMarketValueGroups, bytes) ← CollateralMarketValueGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, collateralMarketValueGroups }, bytes)

theorem encode_length_pos (message : CollateralMarketValue) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : CollateralMarketValue) : (encode message).length ≤ 10214 := by
  have bound_collateralMarketValueGroups := CollateralMarketValueGroups.encode_length_le message.collateralMarketValueGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : CollateralMarketValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [CollateralMarketValueGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : FxLotTypeRulesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FxLotTypeRulesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end FxLotTypeRulesGroup

/-- Fx Lot Type Rules Groups -/
structure FxLotTypeRulesGroups where
  blockLength : BitVec 16
  fxLotTypeRulesGroup : Bounded 1 FxLotTypeRulesGroup
  deriving DecidableEq, Repr

namespace FxLotTypeRulesGroups

def encode (message : FxLotTypeRulesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.fxLotTypeRulesGroup.val.length)
    ++ encodeMany FxLotTypeRulesGroup.encode message.fxLotTypeRulesGroup.val

def decode (bytes : List UInt8) : Option (FxLotTypeRulesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (fxLotTypeRulesGroup_, bytes) ← decodeMany FxLotTypeRulesGroup.decode numInGroup.toNat bytes
  if fits_fxLotTypeRulesGroup : fxLotTypeRulesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, fxLotTypeRulesGroup := ⟨fxLotTypeRulesGroup_, fits_fxLotTypeRulesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : FxLotTypeRulesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FxLotTypeRulesGroups) : (encode message).length ≤ 2298 := by
  have bound_fxLotTypeRulesGroup := message.fxLotTypeRulesGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const FxLotTypeRulesGroup.encode 9 FxLotTypeRulesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : FxLotTypeRulesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 FxLotTypeRulesGroup.encode FxLotTypeRulesGroup.decode FxLotTypeRulesGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.fxLotTypeRulesGroup.length_lt, ↓reduceDIte]
  rfl

end FxLotTypeRulesGroups

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradingSessionsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end TradingSessionsGroup

/-- Trading Sessions Groups -/
structure TradingSessionsGroups where
  blockLength : BitVec 16
  tradingSessionsGroup : Bounded 1 TradingSessionsGroup
  deriving DecidableEq, Repr

namespace TradingSessionsGroups

def encode (message : TradingSessionsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradingSessionsGroup.val.length)
    ++ encodeMany TradingSessionsGroup.encode message.tradingSessionsGroup.val

def decode (bytes : List UInt8) : Option (TradingSessionsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (tradingSessionsGroup_, bytes) ← decodeMany TradingSessionsGroup.decode numInGroup.toNat bytes
  if fits_tradingSessionsGroup : tradingSessionsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, tradingSessionsGroup := ⟨tradingSessionsGroup_, fits_tradingSessionsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradingSessionsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradingSessionsGroups) : (encode message).length ≤ 4593 := by
  have bound_tradingSessionsGroup := message.tradingSessionsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const TradingSessionsGroup.encode 18 TradingSessionsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TradingSessionsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TradingSessionsGroup.encode TradingSessionsGroup.decode TradingSessionsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.tradingSessionsGroup.length_lt, ↓reduceDIte]
  rfl

end TradingSessionsGroups

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
  eventsGroups : EventsGroups
  feedTypesGroups : FeedTypesGroups
  instAttribGroups : InstAttribGroups
  fxLotTypeRulesGroups : FxLotTypeRulesGroups
  tradingSessionsGroups : TradingSessionsGroups
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
    ++ EventsGroups.encode message.eventsGroups
    ++ FeedTypesGroups.encode message.feedTypesGroups
    ++ InstAttribGroups.encode message.instAttribGroups
    ++ FxLotTypeRulesGroups.encode message.fxLotTypeRulesGroups
    ++ TradingSessionsGroups.encode message.tradingSessionsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
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
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  let (feedTypesGroups, bytes) ← FeedTypesGroups.decode bytes
  let (instAttribGroups, bytes) ← InstAttribGroups.decode bytes
  let (fxLotTypeRulesGroups, bytes) ← FxLotTypeRulesGroups.decode bytes
  let (tradingSessionsGroups, bytes) ← TradingSessionsGroups.decode bytes
  pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, currency, settlCurrency, priceQuoteCurrency, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementEx, displayFactor, pricePrecision, unitOfMeasure, unitOfMeasureQty, highLimitPrice, lowLimitPrice, maxPriceVariation, userDefinedInstrument, financialInstrumentFullName, fxCurrencySymbol, settlType, interveningDays, fxBenchmarkRateFix, rateSource, fixRateLocalTime, fixRateLocalTimeZone, minQuoteLife, maxPriceDiscretionOffset, instrumentGuid, maturityMonthYear, settlementLocale, eventsGroups, feedTypesGroups, instAttribGroups, fxLotTypeRulesGroups, tradingSessionsGroups }, bytes)

theorem encode_length_pos (message : MdInstrumentDefinitionFx) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdInstrumentDefinitionFx) : (encode message).length ≤ 11544 := by
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  have bound_feedTypesGroups := FeedTypesGroups.encode_length_le message.feedTypesGroups
  have bound_instAttribGroups := InstAttribGroups.encode_length_le message.instAttribGroups
  have bound_fxLotTypeRulesGroups := FxLotTypeRulesGroups.encode_length_le message.fxLotTypeRulesGroups
  have bound_tradingSessionsGroups := TradingSessionsGroups.encode_length_le message.tradingSessionsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityUpdateAction.encode_length, encodeUInt_length, Alpha.encode_length, MaturityMonthYear.encode_length]
  omega

@[simp] theorem decode_encode (message : MdInstrumentDefinitionFx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [SecurityUpdateAction.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [MaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [EventsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [FeedTypesGroups.decode_encode]
  simp only [Option.bind_some]
  rw [InstAttribGroups.decode_encode]
  simp only [Option.bind_some]
  rw [FxLotTypeRulesGroups.decode_encode]
  simp only [Option.bind_some]
  rw [TradingSessionsGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryTypeBook.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshBookLongGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshBookLongGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MdEntryTypeBook.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshBookLongGroup

/-- Incremental Refresh Book Long Groups -/
structure IncrementalRefreshBookLongGroups where
  blockLength : BitVec 16
  incrementalRefreshBookLongGroup : Bounded 1 IncrementalRefreshBookLongGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshBookLongGroups

def encode (message : IncrementalRefreshBookLongGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshBookLongGroup.val.length)
    ++ encodeMany IncrementalRefreshBookLongGroup.encode message.incrementalRefreshBookLongGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshBookLongGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshBookLongGroup_, bytes) ← decodeMany IncrementalRefreshBookLongGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshBookLongGroup : incrementalRefreshBookLongGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshBookLongGroup := ⟨incrementalRefreshBookLongGroup_, fits_incrementalRefreshBookLongGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshBookLongGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshBookLongGroups) : (encode message).length ≤ 8163 := by
  have bound_incrementalRefreshBookLongGroup := message.incrementalRefreshBookLongGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshBookLongGroup.encode 32 IncrementalRefreshBookLongGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshBookLongGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshBookLongGroup.encode IncrementalRefreshBookLongGroup.decode IncrementalRefreshBookLongGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshBookLongGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshBookLongGroups

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshBookLongOrderIdGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshBookLongOrderIdGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshBookLongOrderIdGroup

/-- Incremental Refresh Book Long Order Id Groups -/
structure IncrementalRefreshBookLongOrderIdGroups where
  blockLength : BitVec 16
  padding5 : Alpha 5
  incrementalRefreshBookLongOrderIdGroup : Bounded 1 IncrementalRefreshBookLongOrderIdGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshBookLongOrderIdGroups

def encode (message : IncrementalRefreshBookLongOrderIdGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ Alpha.encode message.padding5
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshBookLongOrderIdGroup.val.length)
    ++ encodeMany IncrementalRefreshBookLongOrderIdGroup.encode message.incrementalRefreshBookLongOrderIdGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshBookLongOrderIdGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshBookLongOrderIdGroup_, bytes) ← decodeMany IncrementalRefreshBookLongOrderIdGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshBookLongOrderIdGroup : incrementalRefreshBookLongOrderIdGroup_.length < 256 ^ 1 then
    pure ({ blockLength, padding5, incrementalRefreshBookLongOrderIdGroup := ⟨incrementalRefreshBookLongOrderIdGroup_, fits_incrementalRefreshBookLongOrderIdGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshBookLongOrderIdGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshBookLongOrderIdGroups) : (encode message).length ≤ 6128 := by
  have bound_incrementalRefreshBookLongOrderIdGroup := message.incrementalRefreshBookLongOrderIdGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshBookLongOrderIdGroup.encode 24 IncrementalRefreshBookLongOrderIdGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshBookLongOrderIdGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshBookLongOrderIdGroup.encode IncrementalRefreshBookLongOrderIdGroup.decode IncrementalRefreshBookLongOrderIdGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshBookLongOrderIdGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshBookLongOrderIdGroups

/-- Md Incremental Refresh Book Long Qty -/
structure MdIncrementalRefreshBookLongQty where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshBookLongGroups : IncrementalRefreshBookLongGroups
  incrementalRefreshBookLongOrderIdGroups : IncrementalRefreshBookLongOrderIdGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshBookLongQty

def encode (message : MdIncrementalRefreshBookLongQty) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ IncrementalRefreshBookLongGroups.encode message.incrementalRefreshBookLongGroups
    ++ IncrementalRefreshBookLongOrderIdGroups.encode message.incrementalRefreshBookLongOrderIdGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshBookLongQty × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshBookLongGroups, bytes) ← IncrementalRefreshBookLongGroups.decode bytes
  let (incrementalRefreshBookLongOrderIdGroups, bytes) ← IncrementalRefreshBookLongOrderIdGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshBookLongGroups, incrementalRefreshBookLongOrderIdGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshBookLongQty) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshBookLongQty) : (encode message).length ≤ 14302 := by
  have bound_incrementalRefreshBookLongGroups := IncrementalRefreshBookLongGroups.encode_length_le message.incrementalRefreshBookLongGroups
  have bound_incrementalRefreshBookLongOrderIdGroups := IncrementalRefreshBookLongOrderIdGroups.encode_length_le message.incrementalRefreshBookLongOrderIdGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshBookLongQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshBookLongGroups.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshBookLongOrderIdGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryLongGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryLongGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshTradeSummaryLongGroup

/-- Incremental Refresh Trade Summary Long Groups -/
structure IncrementalRefreshTradeSummaryLongGroups where
  blockLength : BitVec 16
  incrementalRefreshTradeSummaryLongGroup : Bounded 1 IncrementalRefreshTradeSummaryLongGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeSummaryLongGroups

def encode (message : IncrementalRefreshTradeSummaryLongGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshTradeSummaryLongGroup.val.length)
    ++ encodeMany IncrementalRefreshTradeSummaryLongGroup.encode message.incrementalRefreshTradeSummaryLongGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeSummaryLongGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTradeSummaryLongGroup_, bytes) ← decodeMany IncrementalRefreshTradeSummaryLongGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshTradeSummaryLongGroup : incrementalRefreshTradeSummaryLongGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshTradeSummaryLongGroup := ⟨incrementalRefreshTradeSummaryLongGroup_, fits_incrementalRefreshTradeSummaryLongGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryLongGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshTradeSummaryLongGroups) : (encode message).length ≤ 10203 := by
  have bound_incrementalRefreshTradeSummaryLongGroup := message.incrementalRefreshTradeSummaryLongGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshTradeSummaryLongGroup.encode 40 IncrementalRefreshTradeSummaryLongGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryLongGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshTradeSummaryLongGroup.encode IncrementalRefreshTradeSummaryLongGroup.decode IncrementalRefreshTradeSummaryLongGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshTradeSummaryLongGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshTradeSummaryLongGroups

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryLongOrderIdGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryLongOrderIdGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshTradeSummaryLongOrderIdGroup

/-- Incremental Refresh Trade Summary Long Order Id Groups -/
structure IncrementalRefreshTradeSummaryLongOrderIdGroups where
  blockLength : BitVec 16
  padding5 : Alpha 5
  incrementalRefreshTradeSummaryLongOrderIdGroup : Bounded 1 IncrementalRefreshTradeSummaryLongOrderIdGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeSummaryLongOrderIdGroups

def encode (message : IncrementalRefreshTradeSummaryLongOrderIdGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ Alpha.encode message.padding5
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshTradeSummaryLongOrderIdGroup.val.length)
    ++ encodeMany IncrementalRefreshTradeSummaryLongOrderIdGroup.encode message.incrementalRefreshTradeSummaryLongOrderIdGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeSummaryLongOrderIdGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTradeSummaryLongOrderIdGroup_, bytes) ← decodeMany IncrementalRefreshTradeSummaryLongOrderIdGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshTradeSummaryLongOrderIdGroup : incrementalRefreshTradeSummaryLongOrderIdGroup_.length < 256 ^ 1 then
    pure ({ blockLength, padding5, incrementalRefreshTradeSummaryLongOrderIdGroup := ⟨incrementalRefreshTradeSummaryLongOrderIdGroup_, fits_incrementalRefreshTradeSummaryLongOrderIdGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryLongOrderIdGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshTradeSummaryLongOrderIdGroups) : (encode message).length ≤ 4088 := by
  have bound_incrementalRefreshTradeSummaryLongOrderIdGroup := message.incrementalRefreshTradeSummaryLongOrderIdGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshTradeSummaryLongOrderIdGroup.encode 16 IncrementalRefreshTradeSummaryLongOrderIdGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryLongOrderIdGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshTradeSummaryLongOrderIdGroup.encode IncrementalRefreshTradeSummaryLongOrderIdGroup.decode IncrementalRefreshTradeSummaryLongOrderIdGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshTradeSummaryLongOrderIdGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshTradeSummaryLongOrderIdGroups

/-- Md Incremental Refresh Trade Summary Long Qty -/
structure MdIncrementalRefreshTradeSummaryLongQty where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshTradeSummaryLongGroups : IncrementalRefreshTradeSummaryLongGroups
  incrementalRefreshTradeSummaryLongOrderIdGroups : IncrementalRefreshTradeSummaryLongOrderIdGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshTradeSummaryLongQty

def encode (message : MdIncrementalRefreshTradeSummaryLongQty) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ IncrementalRefreshTradeSummaryLongGroups.encode message.incrementalRefreshTradeSummaryLongGroups
    ++ IncrementalRefreshTradeSummaryLongOrderIdGroups.encode message.incrementalRefreshTradeSummaryLongOrderIdGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshTradeSummaryLongQty × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshTradeSummaryLongGroups, bytes) ← IncrementalRefreshTradeSummaryLongGroups.decode bytes
  let (incrementalRefreshTradeSummaryLongOrderIdGroups, bytes) ← IncrementalRefreshTradeSummaryLongOrderIdGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshTradeSummaryLongGroups, incrementalRefreshTradeSummaryLongOrderIdGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshTradeSummaryLongQty) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshTradeSummaryLongQty) : (encode message).length ≤ 14302 := by
  have bound_incrementalRefreshTradeSummaryLongGroups := IncrementalRefreshTradeSummaryLongGroups.encode_length_le message.incrementalRefreshTradeSummaryLongGroups
  have bound_incrementalRefreshTradeSummaryLongOrderIdGroups := IncrementalRefreshTradeSummaryLongOrderIdGroups.encode_length_le message.incrementalRefreshTradeSummaryLongOrderIdGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshTradeSummaryLongQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshTradeSummaryLongGroups.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshTradeSummaryLongOrderIdGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshVolumeLongGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshVolumeLongGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshVolumeLongGroup

/-- Incremental Refresh Volume Long Groups -/
structure IncrementalRefreshVolumeLongGroups where
  blockLength : BitVec 16
  incrementalRefreshVolumeLongGroup : Bounded 1 IncrementalRefreshVolumeLongGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshVolumeLongGroups

def encode (message : IncrementalRefreshVolumeLongGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshVolumeLongGroup.val.length)
    ++ encodeMany IncrementalRefreshVolumeLongGroup.encode message.incrementalRefreshVolumeLongGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshVolumeLongGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshVolumeLongGroup_, bytes) ← decodeMany IncrementalRefreshVolumeLongGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshVolumeLongGroup : incrementalRefreshVolumeLongGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshVolumeLongGroup := ⟨incrementalRefreshVolumeLongGroup_, fits_incrementalRefreshVolumeLongGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshVolumeLongGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshVolumeLongGroups) : (encode message).length ≤ 6123 := by
  have bound_incrementalRefreshVolumeLongGroup := message.incrementalRefreshVolumeLongGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshVolumeLongGroup.encode 24 IncrementalRefreshVolumeLongGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshVolumeLongGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshVolumeLongGroup.encode IncrementalRefreshVolumeLongGroup.decode IncrementalRefreshVolumeLongGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshVolumeLongGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshVolumeLongGroups

/-- Md Incremental Refresh Volume Long Qty -/
structure MdIncrementalRefreshVolumeLongQty where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshVolumeLongGroups : IncrementalRefreshVolumeLongGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshVolumeLongQty

def encode (message : MdIncrementalRefreshVolumeLongQty) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ IncrementalRefreshVolumeLongGroups.encode message.incrementalRefreshVolumeLongGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshVolumeLongQty × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshVolumeLongGroups, bytes) ← IncrementalRefreshVolumeLongGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshVolumeLongGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshVolumeLongQty) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshVolumeLongQty) : (encode message).length ≤ 6134 := by
  have bound_incrementalRefreshVolumeLongGroups := IncrementalRefreshVolumeLongGroups.encode_length_le message.incrementalRefreshVolumeLongGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshVolumeLongQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshVolumeLongGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryTypeStatistics.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshSessionStatisticsLongGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshSessionStatisticsLongGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MdEntryTypeStatistics.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshSessionStatisticsLongGroup

/-- Incremental Refresh Session Statistics Long Groups -/
structure IncrementalRefreshSessionStatisticsLongGroups where
  blockLength : BitVec 16
  incrementalRefreshSessionStatisticsLongGroup : Bounded 1 IncrementalRefreshSessionStatisticsLongGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshSessionStatisticsLongGroups

def encode (message : IncrementalRefreshSessionStatisticsLongGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshSessionStatisticsLongGroup.val.length)
    ++ encodeMany IncrementalRefreshSessionStatisticsLongGroup.encode message.incrementalRefreshSessionStatisticsLongGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshSessionStatisticsLongGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshSessionStatisticsLongGroup_, bytes) ← decodeMany IncrementalRefreshSessionStatisticsLongGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshSessionStatisticsLongGroup : incrementalRefreshSessionStatisticsLongGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshSessionStatisticsLongGroup := ⟨incrementalRefreshSessionStatisticsLongGroup_, fits_incrementalRefreshSessionStatisticsLongGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshSessionStatisticsLongGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshSessionStatisticsLongGroups) : (encode message).length ≤ 8163 := by
  have bound_incrementalRefreshSessionStatisticsLongGroup := message.incrementalRefreshSessionStatisticsLongGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshSessionStatisticsLongGroup.encode 32 IncrementalRefreshSessionStatisticsLongGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshSessionStatisticsLongGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshSessionStatisticsLongGroup.encode IncrementalRefreshSessionStatisticsLongGroup.decode IncrementalRefreshSessionStatisticsLongGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshSessionStatisticsLongGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshSessionStatisticsLongGroups

/-- Md Incremental Refresh Session Statistics Long Qty -/
structure MdIncrementalRefreshSessionStatisticsLongQty where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshSessionStatisticsLongGroups : IncrementalRefreshSessionStatisticsLongGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshSessionStatisticsLongQty

def encode (message : MdIncrementalRefreshSessionStatisticsLongQty) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.padding2
    ++ IncrementalRefreshSessionStatisticsLongGroups.encode message.incrementalRefreshSessionStatisticsLongGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshSessionStatisticsLongQty × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshSessionStatisticsLongGroups, bytes) ← IncrementalRefreshSessionStatisticsLongGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshSessionStatisticsLongGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshSessionStatisticsLongQty) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshSessionStatisticsLongQty) : (encode message).length ≤ 8174 := by
  have bound_incrementalRefreshSessionStatisticsLongGroups := IncrementalRefreshSessionStatisticsLongGroups.encode_length_le message.incrementalRefreshSessionStatisticsLongGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshSessionStatisticsLongQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshSessionStatisticsLongGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryType.encode_length]

theorem encode_length_pos (message : SnapshotfullRefreshTcpLongGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotfullRefreshTcpLongGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MdEntryType.decode_encode, Option.bind_some]
  rfl

end SnapshotfullRefreshTcpLongGroup

/-- Snapshotfull Refresh Tcp Long Groups -/
structure SnapshotfullRefreshTcpLongGroups where
  blockLength : BitVec 16
  snapshotfullRefreshTcpLongGroup : Bounded 1 SnapshotfullRefreshTcpLongGroup
  deriving DecidableEq, Repr

namespace SnapshotfullRefreshTcpLongGroups

def encode (message : SnapshotfullRefreshTcpLongGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.snapshotfullRefreshTcpLongGroup.val.length)
    ++ encodeMany SnapshotfullRefreshTcpLongGroup.encode message.snapshotfullRefreshTcpLongGroup.val

def decode (bytes : List UInt8) : Option (SnapshotfullRefreshTcpLongGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotfullRefreshTcpLongGroup_, bytes) ← decodeMany SnapshotfullRefreshTcpLongGroup.decode numInGroup.toNat bytes
  if fits_snapshotfullRefreshTcpLongGroup : snapshotfullRefreshTcpLongGroup_.length < 256 ^ 1 then
    pure ({ blockLength, snapshotfullRefreshTcpLongGroup := ⟨snapshotfullRefreshTcpLongGroup_, fits_snapshotfullRefreshTcpLongGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotfullRefreshTcpLongGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotfullRefreshTcpLongGroups) : (encode message).length ≤ 5868 := by
  have bound_snapshotfullRefreshTcpLongGroup := message.snapshotfullRefreshTcpLongGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SnapshotfullRefreshTcpLongGroup.encode 23 SnapshotfullRefreshTcpLongGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotfullRefreshTcpLongGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SnapshotfullRefreshTcpLongGroup.encode SnapshotfullRefreshTcpLongGroup.decode SnapshotfullRefreshTcpLongGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.snapshotfullRefreshTcpLongGroup.length_lt, ↓reduceDIte]
  rfl

end SnapshotfullRefreshTcpLongGroups

/-- Snapshot Full Refresh Tcp Long Qty -/
structure SnapshotFullRefreshTcpLongQty where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  securityId : BitVec 32
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  snapshotfullRefreshTcpLongGroups : SnapshotfullRefreshTcpLongGroups
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshTcpLongQty

def encode (message : SnapshotFullRefreshTcpLongQty) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 8 message.highLimitPrice
    ++ encodeUIntLE 8 message.lowLimitPrice
    ++ encodeUIntLE 8 message.maxPriceVariation
    ++ SnapshotfullRefreshTcpLongGroups.encode message.snapshotfullRefreshTcpLongGroups

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshTcpLongQty × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (snapshotfullRefreshTcpLongGroups, bytes) ← SnapshotfullRefreshTcpLongGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, securityId, highLimitPrice, lowLimitPrice, maxPriceVariation, snapshotfullRefreshTcpLongGroups }, bytes)

theorem encode_length_pos (message : SnapshotFullRefreshTcpLongQty) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotFullRefreshTcpLongQty) : (encode message).length ≤ 5905 := by
  have bound_snapshotfullRefreshTcpLongGroups := SnapshotfullRefreshTcpLongGroups.encode_length_le message.snapshotfullRefreshTcpLongGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : SnapshotFullRefreshTcpLongQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [SnapshotfullRefreshTcpLongGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryType.encode_length]

theorem encode_length_pos (message : SnapshotFullRefreshLongGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotFullRefreshLongGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MdEntryType.decode_encode, Option.bind_some]
  rfl

end SnapshotFullRefreshLongGroup

/-- Snapshot Full Refresh Long Groups -/
structure SnapshotFullRefreshLongGroups where
  blockLength : BitVec 16
  snapshotFullRefreshLongGroup : Bounded 1 SnapshotFullRefreshLongGroup
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshLongGroups

def encode (message : SnapshotFullRefreshLongGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.snapshotFullRefreshLongGroup.val.length)
    ++ encodeMany SnapshotFullRefreshLongGroup.encode message.snapshotFullRefreshLongGroup.val

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshLongGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotFullRefreshLongGroup_, bytes) ← decodeMany SnapshotFullRefreshLongGroup.decode numInGroup.toNat bytes
  if fits_snapshotFullRefreshLongGroup : snapshotFullRefreshLongGroup_.length < 256 ^ 1 then
    pure ({ blockLength, snapshotFullRefreshLongGroup := ⟨snapshotFullRefreshLongGroup_, fits_snapshotFullRefreshLongGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotFullRefreshLongGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotFullRefreshLongGroups) : (encode message).length ≤ 5868 := by
  have bound_snapshotFullRefreshLongGroup := message.snapshotFullRefreshLongGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SnapshotFullRefreshLongGroup.encode 23 SnapshotFullRefreshLongGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotFullRefreshLongGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SnapshotFullRefreshLongGroup.encode SnapshotFullRefreshLongGroup.decode SnapshotFullRefreshLongGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.snapshotFullRefreshLongGroup.length_lt, ↓reduceDIte]
  rfl

end SnapshotFullRefreshLongGroups

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
  snapshotFullRefreshLongGroups : SnapshotFullRefreshLongGroups
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
    ++ SnapshotFullRefreshLongGroups.encode message.snapshotFullRefreshLongGroups

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
  let (snapshotFullRefreshLongGroups, bytes) ← SnapshotFullRefreshLongGroups.decode bytes
  pure ({ lastMsgSeqNumProcessed, totNumReports, securityId, rptSeq, transactTime, lastUpdateTime, tradeDate, mdSecurityTradingStatus, highLimitPrice, lowLimitPrice, maxPriceVariation, snapshotFullRefreshLongGroups }, bytes)

theorem encode_length_pos (message : SnapshotFullRefreshLongQty) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotFullRefreshLongQty) : (encode message).length ≤ 5927 := by
  have bound_snapshotFullRefreshLongGroups := SnapshotFullRefreshLongGroups.encode_length_le message.snapshotFullRefreshLongGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : SnapshotFullRefreshLongQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [SnapshotFullRefreshLongGroups.decode_encode, Option.bind_some]
  rfl

end SnapshotFullRefreshLongQty

/-- Negotiate: 78 bytes -/
structure Negotiate where
  hmacSignature : Alpha 32
  accessKeyId : Alpha 20
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  session : Alpha 5
  firm : Alpha 5
  deriving DecidableEq, Repr

namespace Negotiate

def encode (message : Negotiate) : List UInt8 :=
  Alpha.encode message.hmacSignature
    ++ Alpha.encode message.accessKeyId
    ++ encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ Alpha.encode message.session
    ++ Alpha.encode message.firm

def decode (bytes : List UInt8) : Option (Negotiate × List UInt8) := do
  let (hmacSignature, bytes) ← Alpha.decode 32 bytes
  let (accessKeyId, bytes) ← Alpha.decode 20 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (session, bytes) ← Alpha.decode 5 bytes
  let (firm, bytes) ← Alpha.decode 5 bytes
  pure ({ hmacSignature, accessKeyId, uuid, requestTimestamp, session, firm }, bytes)

@[simp] theorem encode_length (message : Negotiate) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : Negotiate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Negotiate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end Negotiate

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
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NegotiationReject) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NegotiationReject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : NegotiationResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NegotiationResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : Terminate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Terminate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end Terminate

/-- Market Data Request Security Group: 6 bytes -/
structure MarketDataRequestSecurityGroup where
  securityGroup : Alpha 6
  deriving DecidableEq, Repr

namespace MarketDataRequestSecurityGroup

def encode (message : MarketDataRequestSecurityGroup) : List UInt8 :=
  Alpha.encode message.securityGroup

def decode (bytes : List UInt8) : Option (MarketDataRequestSecurityGroup × List UInt8) := do
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  pure ({ securityGroup }, bytes)

@[simp] theorem encode_length (message : MarketDataRequestSecurityGroup) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : MarketDataRequestSecurityGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDataRequestSecurityGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end MarketDataRequestSecurityGroup

/-- Market Data Request Security Groups -/
structure MarketDataRequestSecurityGroups where
  blockLength : BitVec 16
  marketDataRequestSecurityGroup : Bounded 1 MarketDataRequestSecurityGroup
  deriving DecidableEq, Repr

namespace MarketDataRequestSecurityGroups

def encode (message : MarketDataRequestSecurityGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.marketDataRequestSecurityGroup.val.length)
    ++ encodeMany MarketDataRequestSecurityGroup.encode message.marketDataRequestSecurityGroup.val

def decode (bytes : List UInt8) : Option (MarketDataRequestSecurityGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (marketDataRequestSecurityGroup_, bytes) ← decodeMany MarketDataRequestSecurityGroup.decode numInGroup.toNat bytes
  if fits_marketDataRequestSecurityGroup : marketDataRequestSecurityGroup_.length < 256 ^ 1 then
    pure ({ blockLength, marketDataRequestSecurityGroup := ⟨marketDataRequestSecurityGroup_, fits_marketDataRequestSecurityGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketDataRequestSecurityGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketDataRequestSecurityGroups) : (encode message).length ≤ 1533 := by
  have bound_marketDataRequestSecurityGroup := message.marketDataRequestSecurityGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const MarketDataRequestSecurityGroup.encode 6 MarketDataRequestSecurityGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketDataRequestSecurityGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 MarketDataRequestSecurityGroup.encode MarketDataRequestSecurityGroup.decode MarketDataRequestSecurityGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.marketDataRequestSecurityGroup.length_lt, ↓reduceDIte]
  rfl

end MarketDataRequestSecurityGroups

/-- Market Data Request Related Symbol Group: 4 bytes -/
structure MarketDataRequestRelatedSymbolGroup where
  securityId : BitVec 32
  deriving DecidableEq, Repr

namespace MarketDataRequestRelatedSymbolGroup

def encode (message : MarketDataRequestRelatedSymbolGroup) : List UInt8 :=
  encodeUIntLE 4 message.securityId

def decode (bytes : List UInt8) : Option (MarketDataRequestRelatedSymbolGroup × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId }, bytes)

@[simp] theorem encode_length (message : MarketDataRequestRelatedSymbolGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : MarketDataRequestRelatedSymbolGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDataRequestRelatedSymbolGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end MarketDataRequestRelatedSymbolGroup

/-- Market Data Request Related Symbol Groups -/
structure MarketDataRequestRelatedSymbolGroups where
  blockLength : BitVec 16
  marketDataRequestRelatedSymbolGroup : Bounded 1 MarketDataRequestRelatedSymbolGroup
  deriving DecidableEq, Repr

namespace MarketDataRequestRelatedSymbolGroups

def encode (message : MarketDataRequestRelatedSymbolGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.marketDataRequestRelatedSymbolGroup.val.length)
    ++ encodeMany MarketDataRequestRelatedSymbolGroup.encode message.marketDataRequestRelatedSymbolGroup.val

def decode (bytes : List UInt8) : Option (MarketDataRequestRelatedSymbolGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (marketDataRequestRelatedSymbolGroup_, bytes) ← decodeMany MarketDataRequestRelatedSymbolGroup.decode numInGroup.toNat bytes
  if fits_marketDataRequestRelatedSymbolGroup : marketDataRequestRelatedSymbolGroup_.length < 256 ^ 1 then
    pure ({ blockLength, marketDataRequestRelatedSymbolGroup := ⟨marketDataRequestRelatedSymbolGroup_, fits_marketDataRequestRelatedSymbolGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketDataRequestRelatedSymbolGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketDataRequestRelatedSymbolGroups) : (encode message).length ≤ 1023 := by
  have bound_marketDataRequestRelatedSymbolGroup := message.marketDataRequestRelatedSymbolGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const MarketDataRequestRelatedSymbolGroup.encode 4 MarketDataRequestRelatedSymbolGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketDataRequestRelatedSymbolGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 MarketDataRequestRelatedSymbolGroup.encode MarketDataRequestRelatedSymbolGroup.decode MarketDataRequestRelatedSymbolGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.marketDataRequestRelatedSymbolGroup.length_lt, ↓reduceDIte]
  rfl

end MarketDataRequestRelatedSymbolGroups

/-- Market Data Request -/
structure MarketDataRequest where
  mdReqId : BitVec 32
  subscriptionReqType : BitVec 8
  marketDataRequestSecurityGroups : MarketDataRequestSecurityGroups
  marketDataRequestRelatedSymbolGroups : MarketDataRequestRelatedSymbolGroups
  deriving DecidableEq, Repr

namespace MarketDataRequest

def encode (message : MarketDataRequest) : List UInt8 :=
  encodeUIntLE 4 message.mdReqId
    ++ encodeUInt 1 message.subscriptionReqType
    ++ MarketDataRequestSecurityGroups.encode message.marketDataRequestSecurityGroups
    ++ MarketDataRequestRelatedSymbolGroups.encode message.marketDataRequestRelatedSymbolGroups

def decode (bytes : List UInt8) : Option (MarketDataRequest × List UInt8) := do
  let (mdReqId, bytes) ← decodeUIntLE 4 bytes
  let (subscriptionReqType, bytes) ← decodeUInt 1 bytes
  let (marketDataRequestSecurityGroups, bytes) ← MarketDataRequestSecurityGroups.decode bytes
  let (marketDataRequestRelatedSymbolGroups, bytes) ← MarketDataRequestRelatedSymbolGroups.decode bytes
  pure ({ mdReqId, subscriptionReqType, marketDataRequestSecurityGroups, marketDataRequestRelatedSymbolGroups }, bytes)

theorem encode_length_pos (message : MarketDataRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketDataRequest) : (encode message).length ≤ 2561 := by
  have bound_marketDataRequestSecurityGroups := MarketDataRequestSecurityGroups.encode_length_le message.marketDataRequestSecurityGroups
  have bound_marketDataRequestRelatedSymbolGroups := MarketDataRequestRelatedSymbolGroups.encode_length_le message.marketDataRequestRelatedSymbolGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : MarketDataRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MarketDataRequestSecurityGroups.decode_encode]
  simp only [Option.bind_some]
  rw [MarketDataRequestRelatedSymbolGroups.decode_encode, Option.bind_some]
  rfl

end MarketDataRequest

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
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : RequestAckSecurityGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestAckSecurityGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end RequestAckSecurityGroup

/-- Request Ack Security Groups -/
structure RequestAckSecurityGroups where
  blockLength : BitVec 16
  requestAckSecurityGroup : Bounded 1 RequestAckSecurityGroup
  deriving DecidableEq, Repr

namespace RequestAckSecurityGroups

def encode (message : RequestAckSecurityGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.requestAckSecurityGroup.val.length)
    ++ encodeMany RequestAckSecurityGroup.encode message.requestAckSecurityGroup.val

def decode (bytes : List UInt8) : Option (RequestAckSecurityGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (requestAckSecurityGroup_, bytes) ← decodeMany RequestAckSecurityGroup.decode numInGroup.toNat bytes
  if fits_requestAckSecurityGroup : requestAckSecurityGroup_.length < 256 ^ 1 then
    pure ({ blockLength, requestAckSecurityGroup := ⟨requestAckSecurityGroup_, fits_requestAckSecurityGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : RequestAckSecurityGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RequestAckSecurityGroups) : (encode message).length ≤ 1533 := by
  have bound_requestAckSecurityGroup := message.requestAckSecurityGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const RequestAckSecurityGroup.encode 6 RequestAckSecurityGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : RequestAckSecurityGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 RequestAckSecurityGroup.encode RequestAckSecurityGroup.decode RequestAckSecurityGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.requestAckSecurityGroup.length_lt, ↓reduceDIte]
  rfl

end RequestAckSecurityGroups

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
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : RequestAckRelatedSymbolGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestAckRelatedSymbolGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end RequestAckRelatedSymbolGroup

/-- Request Ack Related Symbol Groups -/
structure RequestAckRelatedSymbolGroups where
  blockLength : BitVec 16
  requestAckRelatedSymbolGroup : Bounded 1 RequestAckRelatedSymbolGroup
  deriving DecidableEq, Repr

namespace RequestAckRelatedSymbolGroups

def encode (message : RequestAckRelatedSymbolGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.requestAckRelatedSymbolGroup.val.length)
    ++ encodeMany RequestAckRelatedSymbolGroup.encode message.requestAckRelatedSymbolGroup.val

def decode (bytes : List UInt8) : Option (RequestAckRelatedSymbolGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (requestAckRelatedSymbolGroup_, bytes) ← decodeMany RequestAckRelatedSymbolGroup.decode numInGroup.toNat bytes
  if fits_requestAckRelatedSymbolGroup : requestAckRelatedSymbolGroup_.length < 256 ^ 1 then
    pure ({ blockLength, requestAckRelatedSymbolGroup := ⟨requestAckRelatedSymbolGroup_, fits_requestAckRelatedSymbolGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : RequestAckRelatedSymbolGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RequestAckRelatedSymbolGroups) : (encode message).length ≤ 1023 := by
  have bound_requestAckRelatedSymbolGroup := message.requestAckRelatedSymbolGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const RequestAckRelatedSymbolGroup.encode 4 RequestAckRelatedSymbolGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : RequestAckRelatedSymbolGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 RequestAckRelatedSymbolGroup.encode RequestAckRelatedSymbolGroup.decode RequestAckRelatedSymbolGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.requestAckRelatedSymbolGroup.length_lt, ↓reduceDIte]
  rfl

end RequestAckRelatedSymbolGroups

/-- Request Ack -/
structure RequestAck where
  mdReqId : BitVec 32
  subscriptionReqType : BitVec 8
  mdReqIdStatus : BitVec 8
  requestAckSecurityGroups : RequestAckSecurityGroups
  requestAckRelatedSymbolGroups : RequestAckRelatedSymbolGroups
  deriving DecidableEq, Repr

namespace RequestAck

def encode (message : RequestAck) : List UInt8 :=
  encodeUIntLE 4 message.mdReqId
    ++ encodeUInt 1 message.subscriptionReqType
    ++ encodeUInt 1 message.mdReqIdStatus
    ++ RequestAckSecurityGroups.encode message.requestAckSecurityGroups
    ++ RequestAckRelatedSymbolGroups.encode message.requestAckRelatedSymbolGroups

def decode (bytes : List UInt8) : Option (RequestAck × List UInt8) := do
  let (mdReqId, bytes) ← decodeUIntLE 4 bytes
  let (subscriptionReqType, bytes) ← decodeUInt 1 bytes
  let (mdReqIdStatus, bytes) ← decodeUInt 1 bytes
  let (requestAckSecurityGroups, bytes) ← RequestAckSecurityGroups.decode bytes
  let (requestAckRelatedSymbolGroups, bytes) ← RequestAckRelatedSymbolGroups.decode bytes
  pure ({ mdReqId, subscriptionReqType, mdReqIdStatus, requestAckSecurityGroups, requestAckRelatedSymbolGroups }, bytes)

theorem encode_length_pos (message : RequestAck) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RequestAck) : (encode message).length ≤ 2562 := by
  have bound_requestAckSecurityGroups := RequestAckSecurityGroups.encode_length_le message.requestAckSecurityGroups
  have bound_requestAckRelatedSymbolGroups := RequestAckRelatedSymbolGroups.encode_length_le message.requestAckRelatedSymbolGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : RequestAck) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [RequestAckSecurityGroups.decode_encode]
  simp only [Option.bind_some]
  rw [RequestAckRelatedSymbolGroups.decode_encode, Option.bind_some]
  rfl

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
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RequestReject) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestReject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end RequestReject

/-- Security List Request Security Group: 6 bytes -/
structure SecurityListRequestSecurityGroup where
  securityGroup : Alpha 6
  deriving DecidableEq, Repr

namespace SecurityListRequestSecurityGroup

def encode (message : SecurityListRequestSecurityGroup) : List UInt8 :=
  Alpha.encode message.securityGroup

def decode (bytes : List UInt8) : Option (SecurityListRequestSecurityGroup × List UInt8) := do
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  pure ({ securityGroup }, bytes)

@[simp] theorem encode_length (message : SecurityListRequestSecurityGroup) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SecurityListRequestSecurityGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityListRequestSecurityGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end SecurityListRequestSecurityGroup

/-- Security List Request Security Groups -/
structure SecurityListRequestSecurityGroups where
  blockLength : BitVec 16
  securityListRequestSecurityGroup : Bounded 1 SecurityListRequestSecurityGroup
  deriving DecidableEq, Repr

namespace SecurityListRequestSecurityGroups

def encode (message : SecurityListRequestSecurityGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityListRequestSecurityGroup.val.length)
    ++ encodeMany SecurityListRequestSecurityGroup.encode message.securityListRequestSecurityGroup.val

def decode (bytes : List UInt8) : Option (SecurityListRequestSecurityGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityListRequestSecurityGroup_, bytes) ← decodeMany SecurityListRequestSecurityGroup.decode numInGroup.toNat bytes
  if fits_securityListRequestSecurityGroup : securityListRequestSecurityGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityListRequestSecurityGroup := ⟨securityListRequestSecurityGroup_, fits_securityListRequestSecurityGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityListRequestSecurityGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityListRequestSecurityGroups) : (encode message).length ≤ 1533 := by
  have bound_securityListRequestSecurityGroup := message.securityListRequestSecurityGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityListRequestSecurityGroup.encode 6 SecurityListRequestSecurityGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityListRequestSecurityGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SecurityListRequestSecurityGroup.encode SecurityListRequestSecurityGroup.decode SecurityListRequestSecurityGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.securityListRequestSecurityGroup.length_lt, ↓reduceDIte]
  rfl

end SecurityListRequestSecurityGroups

/-- Security List Request Related Symbol Group: 4 bytes -/
structure SecurityListRequestRelatedSymbolGroup where
  securityId : BitVec 32
  deriving DecidableEq, Repr

namespace SecurityListRequestRelatedSymbolGroup

def encode (message : SecurityListRequestRelatedSymbolGroup) : List UInt8 :=
  encodeUIntLE 4 message.securityId

def decode (bytes : List UInt8) : Option (SecurityListRequestRelatedSymbolGroup × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId }, bytes)

@[simp] theorem encode_length (message : SecurityListRequestRelatedSymbolGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SecurityListRequestRelatedSymbolGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityListRequestRelatedSymbolGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end SecurityListRequestRelatedSymbolGroup

/-- Security List Request Related Symbol Groups -/
structure SecurityListRequestRelatedSymbolGroups where
  blockLength : BitVec 16
  securityListRequestRelatedSymbolGroup : Bounded 1 SecurityListRequestRelatedSymbolGroup
  deriving DecidableEq, Repr

namespace SecurityListRequestRelatedSymbolGroups

def encode (message : SecurityListRequestRelatedSymbolGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityListRequestRelatedSymbolGroup.val.length)
    ++ encodeMany SecurityListRequestRelatedSymbolGroup.encode message.securityListRequestRelatedSymbolGroup.val

def decode (bytes : List UInt8) : Option (SecurityListRequestRelatedSymbolGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityListRequestRelatedSymbolGroup_, bytes) ← decodeMany SecurityListRequestRelatedSymbolGroup.decode numInGroup.toNat bytes
  if fits_securityListRequestRelatedSymbolGroup : securityListRequestRelatedSymbolGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityListRequestRelatedSymbolGroup := ⟨securityListRequestRelatedSymbolGroup_, fits_securityListRequestRelatedSymbolGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityListRequestRelatedSymbolGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityListRequestRelatedSymbolGroups) : (encode message).length ≤ 1023 := by
  have bound_securityListRequestRelatedSymbolGroup := message.securityListRequestRelatedSymbolGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityListRequestRelatedSymbolGroup.encode 4 SecurityListRequestRelatedSymbolGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityListRequestRelatedSymbolGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SecurityListRequestRelatedSymbolGroup.encode SecurityListRequestRelatedSymbolGroup.decode SecurityListRequestRelatedSymbolGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.securityListRequestRelatedSymbolGroup.length_lt, ↓reduceDIte]
  rfl

end SecurityListRequestRelatedSymbolGroups

/-- Security List Request -/
structure SecurityListRequest where
  mdReqId : BitVec 32
  subscriptionReqType : BitVec 8
  securityListRequestSecurityGroups : SecurityListRequestSecurityGroups
  securityListRequestRelatedSymbolGroups : SecurityListRequestRelatedSymbolGroups
  deriving DecidableEq, Repr

namespace SecurityListRequest

def encode (message : SecurityListRequest) : List UInt8 :=
  encodeUIntLE 4 message.mdReqId
    ++ encodeUInt 1 message.subscriptionReqType
    ++ SecurityListRequestSecurityGroups.encode message.securityListRequestSecurityGroups
    ++ SecurityListRequestRelatedSymbolGroups.encode message.securityListRequestRelatedSymbolGroups

def decode (bytes : List UInt8) : Option (SecurityListRequest × List UInt8) := do
  let (mdReqId, bytes) ← decodeUIntLE 4 bytes
  let (subscriptionReqType, bytes) ← decodeUInt 1 bytes
  let (securityListRequestSecurityGroups, bytes) ← SecurityListRequestSecurityGroups.decode bytes
  let (securityListRequestRelatedSymbolGroups, bytes) ← SecurityListRequestRelatedSymbolGroups.decode bytes
  pure ({ mdReqId, subscriptionReqType, securityListRequestSecurityGroups, securityListRequestRelatedSymbolGroups }, bytes)

theorem encode_length_pos (message : SecurityListRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityListRequest) : (encode message).length ≤ 2561 := by
  have bound_securityListRequestSecurityGroups := SecurityListRequestSecurityGroups.encode_length_le message.securityListRequestSecurityGroups
  have bound_securityListRequestRelatedSymbolGroups := SecurityListRequestRelatedSymbolGroups.encode_length_le message.securityListRequestRelatedSymbolGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : SecurityListRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [SecurityListRequestSecurityGroups.decode_encode]
  simp only [Option.bind_some]
  rw [SecurityListRequestRelatedSymbolGroups.decode_encode, Option.bind_some]
  rfl

end SecurityListRequest

/-- Security Status Request Security Group: 6 bytes -/
structure SecurityStatusRequestSecurityGroup where
  securityGroup : Alpha 6
  deriving DecidableEq, Repr

namespace SecurityStatusRequestSecurityGroup

def encode (message : SecurityStatusRequestSecurityGroup) : List UInt8 :=
  Alpha.encode message.securityGroup

def decode (bytes : List UInt8) : Option (SecurityStatusRequestSecurityGroup × List UInt8) := do
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  pure ({ securityGroup }, bytes)

@[simp] theorem encode_length (message : SecurityStatusRequestSecurityGroup) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SecurityStatusRequestSecurityGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusRequestSecurityGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end SecurityStatusRequestSecurityGroup

/-- Security Status Request Security Groups -/
structure SecurityStatusRequestSecurityGroups where
  blockLength : BitVec 16
  securityStatusRequestSecurityGroup : Bounded 1 SecurityStatusRequestSecurityGroup
  deriving DecidableEq, Repr

namespace SecurityStatusRequestSecurityGroups

def encode (message : SecurityStatusRequestSecurityGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityStatusRequestSecurityGroup.val.length)
    ++ encodeMany SecurityStatusRequestSecurityGroup.encode message.securityStatusRequestSecurityGroup.val

def decode (bytes : List UInt8) : Option (SecurityStatusRequestSecurityGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityStatusRequestSecurityGroup_, bytes) ← decodeMany SecurityStatusRequestSecurityGroup.decode numInGroup.toNat bytes
  if fits_securityStatusRequestSecurityGroup : securityStatusRequestSecurityGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityStatusRequestSecurityGroup := ⟨securityStatusRequestSecurityGroup_, fits_securityStatusRequestSecurityGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityStatusRequestSecurityGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityStatusRequestSecurityGroups) : (encode message).length ≤ 1533 := by
  have bound_securityStatusRequestSecurityGroup := message.securityStatusRequestSecurityGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityStatusRequestSecurityGroup.encode 6 SecurityStatusRequestSecurityGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityStatusRequestSecurityGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SecurityStatusRequestSecurityGroup.encode SecurityStatusRequestSecurityGroup.decode SecurityStatusRequestSecurityGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.securityStatusRequestSecurityGroup.length_lt, ↓reduceDIte]
  rfl

end SecurityStatusRequestSecurityGroups

/-- Security Status Request Related Symbol Group: 4 bytes -/
structure SecurityStatusRequestRelatedSymbolGroup where
  securityId : BitVec 32
  deriving DecidableEq, Repr

namespace SecurityStatusRequestRelatedSymbolGroup

def encode (message : SecurityStatusRequestRelatedSymbolGroup) : List UInt8 :=
  encodeUIntLE 4 message.securityId

def decode (bytes : List UInt8) : Option (SecurityStatusRequestRelatedSymbolGroup × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId }, bytes)

@[simp] theorem encode_length (message : SecurityStatusRequestRelatedSymbolGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SecurityStatusRequestRelatedSymbolGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusRequestRelatedSymbolGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end SecurityStatusRequestRelatedSymbolGroup

/-- Security Status Request Related Symbol Groups -/
structure SecurityStatusRequestRelatedSymbolGroups where
  blockLength : BitVec 16
  securityStatusRequestRelatedSymbolGroup : Bounded 1 SecurityStatusRequestRelatedSymbolGroup
  deriving DecidableEq, Repr

namespace SecurityStatusRequestRelatedSymbolGroups

def encode (message : SecurityStatusRequestRelatedSymbolGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityStatusRequestRelatedSymbolGroup.val.length)
    ++ encodeMany SecurityStatusRequestRelatedSymbolGroup.encode message.securityStatusRequestRelatedSymbolGroup.val

def decode (bytes : List UInt8) : Option (SecurityStatusRequestRelatedSymbolGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityStatusRequestRelatedSymbolGroup_, bytes) ← decodeMany SecurityStatusRequestRelatedSymbolGroup.decode numInGroup.toNat bytes
  if fits_securityStatusRequestRelatedSymbolGroup : securityStatusRequestRelatedSymbolGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityStatusRequestRelatedSymbolGroup := ⟨securityStatusRequestRelatedSymbolGroup_, fits_securityStatusRequestRelatedSymbolGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityStatusRequestRelatedSymbolGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityStatusRequestRelatedSymbolGroups) : (encode message).length ≤ 1023 := by
  have bound_securityStatusRequestRelatedSymbolGroup := message.securityStatusRequestRelatedSymbolGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityStatusRequestRelatedSymbolGroup.encode 4 SecurityStatusRequestRelatedSymbolGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityStatusRequestRelatedSymbolGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SecurityStatusRequestRelatedSymbolGroup.encode SecurityStatusRequestRelatedSymbolGroup.decode SecurityStatusRequestRelatedSymbolGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.securityStatusRequestRelatedSymbolGroup.length_lt, ↓reduceDIte]
  rfl

end SecurityStatusRequestRelatedSymbolGroups

/-- Security Status Request -/
structure SecurityStatusRequest where
  mdReqId : BitVec 32
  subscriptionReqType : BitVec 8
  securityStatusRequestSecurityGroups : SecurityStatusRequestSecurityGroups
  securityStatusRequestRelatedSymbolGroups : SecurityStatusRequestRelatedSymbolGroups
  deriving DecidableEq, Repr

namespace SecurityStatusRequest

def encode (message : SecurityStatusRequest) : List UInt8 :=
  encodeUIntLE 4 message.mdReqId
    ++ encodeUInt 1 message.subscriptionReqType
    ++ SecurityStatusRequestSecurityGroups.encode message.securityStatusRequestSecurityGroups
    ++ SecurityStatusRequestRelatedSymbolGroups.encode message.securityStatusRequestRelatedSymbolGroups

def decode (bytes : List UInt8) : Option (SecurityStatusRequest × List UInt8) := do
  let (mdReqId, bytes) ← decodeUIntLE 4 bytes
  let (subscriptionReqType, bytes) ← decodeUInt 1 bytes
  let (securityStatusRequestSecurityGroups, bytes) ← SecurityStatusRequestSecurityGroups.decode bytes
  let (securityStatusRequestRelatedSymbolGroups, bytes) ← SecurityStatusRequestRelatedSymbolGroups.decode bytes
  pure ({ mdReqId, subscriptionReqType, securityStatusRequestSecurityGroups, securityStatusRequestRelatedSymbolGroups }, bytes)

theorem encode_length_pos (message : SecurityStatusRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityStatusRequest) : (encode message).length ≤ 2561 := by
  have bound_securityStatusRequestSecurityGroups := SecurityStatusRequestSecurityGroups.encode_length_le message.securityStatusRequestSecurityGroups
  have bound_securityStatusRequestRelatedSymbolGroups := SecurityStatusRequestRelatedSymbolGroups.encode_length_le message.securityStatusRequestRelatedSymbolGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : SecurityStatusRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [SecurityStatusRequestSecurityGroups.decode_encode]
  simp only [Option.bind_some]
  rw [SecurityStatusRequestRelatedSymbolGroups.decode_encode, Option.bind_some]
  rfl

end SecurityStatusRequest

/-- Subscriber Heartbeat: 0 bytes -/
structure SubscriberHeartbeat where
  deriving DecidableEq, Repr

namespace SubscriberHeartbeat

def encode (_ : SubscriberHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SubscriberHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SubscriberHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SubscriberHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end SubscriberHeartbeat

/-- Any Payload, selected by Template Id -/
inductive Payload where
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
  | negotiate (message : Negotiate) -- 200
  | negotiationReject (message : NegotiationReject) -- 201
  | negotiationResponse (message : NegotiationResponse) -- 202
  | terminate (message : Terminate) -- 203
  | marketDataRequest (message : MarketDataRequest) -- 205
  | requestAck (message : RequestAck) -- 206
  | requestReject (message : RequestReject) -- 207
  | securityListRequest (message : SecurityListRequest) -- 208
  | securityStatusRequest (message : SecurityStatusRequest) -- 209
  | subscriberHeartbeat (message : SubscriberHeartbeat) -- 210
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
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
  | .negotiate _ => 200
  | .negotiationReject _ => 201
  | .negotiationResponse _ => 202
  | .terminate _ => 203
  | .marketDataRequest _ => 205
  | .requestAck _ => 206
  | .requestReject _ => 207
  | .securityListRequest _ => 208
  | .securityStatusRequest _ => 209
  | .subscriberHeartbeat _ => 210

def encode : Payload → List UInt8
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
  | .negotiate message => Negotiate.encode message
  | .negotiationReject message => NegotiationReject.encode message
  | .negotiationResponse message => NegotiationResponse.encode message
  | .terminate message => Terminate.encode message
  | .marketDataRequest message => MarketDataRequest.encode message
  | .requestAck message => RequestAck.encode message
  | .requestReject message => RequestReject.encode message
  | .securityListRequest message => SecurityListRequest.encode message
  | .securityStatusRequest message => SecurityStatusRequest.encode message
  | .subscriberHeartbeat message => SubscriberHeartbeat.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
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
  else if tag = 200 then (Negotiate.decode bytes).map fun (message, rest) => (.negotiate message, rest)
  else if tag = 201 then (NegotiationReject.decode bytes).map fun (message, rest) => (.negotiationReject message, rest)
  else if tag = 202 then (NegotiationResponse.decode bytes).map fun (message, rest) => (.negotiationResponse message, rest)
  else if tag = 203 then (Terminate.decode bytes).map fun (message, rest) => (.terminate message, rest)
  else if tag = 205 then (MarketDataRequest.decode bytes).map fun (message, rest) => (.marketDataRequest message, rest)
  else if tag = 206 then (RequestAck.decode bytes).map fun (message, rest) => (.requestAck message, rest)
  else if tag = 207 then (RequestReject.decode bytes).map fun (message, rest) => (.requestReject message, rest)
  else if tag = 208 then (SecurityListRequest.decode bytes).map fun (message, rest) => (.securityListRequest message, rest)
  else if tag = 209 then (SecurityStatusRequest.decode bytes).map fun (message, rest) => (.securityStatusRequest message, rest)
  else if tag = 210 then (SubscriberHeartbeat.decode bytes).map fun (message, rest) => (.subscriberHeartbeat message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUIntLE 2 (Payload.tag message.payload)
    ++ encodeUIntLE 2 message.schemaId
    ++ encodeUIntLE 2 message.version
    ++ Payload.encode message.payload

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Payload.decode_encode, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | channelReset inner =>
    have bound_inner := ChannelReset.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | adminHeartbeat inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AdminHeartbeat.encode_length]
    omega
  | adminLogin inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AdminLogin.encode_length]
    omega
  | adminLogout inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AdminLogout.encode_length]
    omega
  | securityStatus inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SecurityStatus.encode_length]
    omega
  | mdIncrementalRefreshVolume inner =>
    have bound_inner := MdIncrementalRefreshVolume.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | quoteRequest inner =>
    have bound_inner := QuoteRequest.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshBook inner =>
    have bound_inner := MdIncrementalRefreshBook.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshOrderBook inner =>
    have bound_inner := MdIncrementalRefreshOrderBook.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshTradeSummary inner =>
    have bound_inner := MdIncrementalRefreshTradeSummary.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshDailyStatistics inner =>
    have bound_inner := MdIncrementalRefreshDailyStatistics.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshLimitsBanding inner =>
    have bound_inner := MdIncrementalRefreshLimitsBanding.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshSessionStatistics inner =>
    have bound_inner := MdIncrementalRefreshSessionStatistics.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | snapshotFullRefresh inner =>
    have bound_inner := SnapshotFullRefresh.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | snapshotFullRefreshOrderBook inner =>
    have bound_inner := SnapshotFullRefreshOrderBook.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdInstrumentDefinitionFuture inner =>
    have bound_inner := MdInstrumentDefinitionFuture.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdInstrumentDefinitionOption inner =>
    have bound_inner := MdInstrumentDefinitionOption.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdInstrumentDefinitionSpread inner =>
    have bound_inner := MdInstrumentDefinitionSpread.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdInstrumentDefinitionFixedIncome inner =>
    have bound_inner := MdInstrumentDefinitionFixedIncome.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdInstrumentDefinitionRepo inner =>
    have bound_inner := MdInstrumentDefinitionRepo.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | snapshotRefreshTopOrders inner =>
    have bound_inner := SnapshotRefreshTopOrders.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | securityStatusWorkup inner =>
    have bound_inner := SecurityStatusWorkup.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | snapshotFullRefreshTcp inner =>
    have bound_inner := SnapshotFullRefreshTcp.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | collateralMarketValue inner =>
    have bound_inner := CollateralMarketValue.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdInstrumentDefinitionFx inner =>
    have bound_inner := MdInstrumentDefinitionFx.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshBookLongQty inner =>
    have bound_inner := MdIncrementalRefreshBookLongQty.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshTradeSummaryLongQty inner =>
    have bound_inner := MdIncrementalRefreshTradeSummaryLongQty.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshVolumeLongQty inner =>
    have bound_inner := MdIncrementalRefreshVolumeLongQty.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshSessionStatisticsLongQty inner =>
    have bound_inner := MdIncrementalRefreshSessionStatisticsLongQty.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | snapshotFullRefreshTcpLongQty inner =>
    have bound_inner := SnapshotFullRefreshTcpLongQty.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | snapshotFullRefreshLongQty inner =>
    have bound_inner := SnapshotFullRefreshLongQty.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | negotiate inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, Negotiate.encode_length]
    omega
  | negotiationReject inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, NegotiationReject.encode_length]
    omega
  | negotiationResponse inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, NegotiationResponse.encode_length]
    omega
  | terminate inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, Terminate.encode_length]
    omega
  | marketDataRequest inner =>
    have bound_inner := MarketDataRequest.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | requestAck inner =>
    have bound_inner := RequestAck.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | requestReject inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RequestReject.encode_length]
    omega
  | securityListRequest inner =>
    have bound_inner := SecurityListRequest.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | securityStatusRequest inner =>
    have bound_inner := SecurityStatusRequest.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | subscriberHeartbeat inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SubscriberHeartbeat.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Udp Packet -/
structure UdpPacket where
  binaryPacketHeader : BinaryPacketHeader
  message : List Message
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  BinaryPacketHeader.encode message.binaryPacketHeader
    ++ encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option UdpPacket := do
  let (binaryPacketHeader, bytes) ← BinaryPacketHeader.decode bytes
  let message ← decodeAll Message.decode bytes.length bytes
  pure { binaryPacketHeader, message }

theorem encode_length_pos (message : UdpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [BinaryPacketHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : UdpPacket) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [BinaryPacketHeader.decode_encode]
  simp only [Option.bind_some]
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), Option.bind_some]
  rfl

end UdpPacket

end Omi.CmeGlobexMdp3SbeV112Udp
