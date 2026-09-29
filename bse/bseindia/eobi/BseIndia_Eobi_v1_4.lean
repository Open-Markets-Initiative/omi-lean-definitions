import Omi.Wire

/-!
# BSE Limited Enhanced Order Book Interface v1.4

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BseBseindiaEobiFbeV14

/-- Eobi Header: 8 bytes -/
structure EobiHeader where
  bodyLen : BitVec 16
  templateId : BitVec 16
  msgSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace EobiHeader

def encode (message : EobiHeader) : List UInt8 :=
  encodeUIntLE 2 message.bodyLen
    ++ (encodeUIntLE 2 message.templateId
    ++ (encodeUIntLE 4 message.msgSeqNum))

def decode (bytes : List UInt8) : Option (EobiHeader × List UInt8) := do
  let (bodyLen, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ bodyLen, templateId, msgSeqNum }, bytes)

@[simp] theorem encode_length (message : EobiHeader) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : EobiHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EobiHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EobiHeader

/-- Packet Header: 32 bytes -/
structure PacketHeader where
  eobiHeader : EobiHeader
  applSeqNum : BitVec 32
  marketSegmentId : BitVec 32
  partitionId : BitVec 8
  completionIndicator : BitVec 8
  applSeqResetIndicator : BitVec 8
  pad5 : Alpha 5
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace PacketHeader

def encode (message : PacketHeader) : List UInt8 :=
  EobiHeader.encode message.eobiHeader
    ++ (encodeUIntLE 4 message.applSeqNum
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 1 message.partitionId
    ++ (encodeUIntLE 1 message.completionIndicator
    ++ (encodeUIntLE 1 message.applSeqResetIndicator
    ++ (Alpha.encode message.pad5
    ++ (encodeUIntLE 8 message.transactTime)))))))

def decode (bytes : List UInt8) : Option (PacketHeader × List UInt8) := do
  let (eobiHeader, bytes) ← EobiHeader.decode bytes
  let (applSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 1 bytes
  let (completionIndicator, bytes) ← decodeUIntLE 1 bytes
  let (applSeqResetIndicator, bytes) ← decodeUIntLE 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ eobiHeader, applSeqNum, marketSegmentId, partitionId, completionIndicator, applSeqResetIndicator, pad5, transactTime }, bytes)

@[simp] theorem encode_length (message : PacketHeader) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, EobiHeader.encode_length, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : PacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PacketHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, EobiHeader.decode_encode, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end PacketHeader

/-- Heartbeat Message: 8 bytes -/
structure HeartbeatMessage where
  lastMsgSeqNumProcessed : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (message : HeartbeatMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastMsgSeqNumProcessed
    ++ (Alpha.encode message.pad4)

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) := do
  let (lastMsgSeqNumProcessed, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ lastMsgSeqNumProcessed, pad4 }, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : HeartbeatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end HeartbeatMessage

/-- Product Summary Message: 8 bytes -/
structure ProductSummaryMessage where
  lastMsgSeqNumProcessed : BitVec 32
  tradingSessionId : BitVec 8
  tradingSessionSubId : BitVec 8
  tradSesStatus : BitVec 8
  fastMarketIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace ProductSummaryMessage

def encode (message : ProductSummaryMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastMsgSeqNumProcessed
    ++ (encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 1 message.tradingSessionSubId
    ++ (encodeUIntLE 1 message.tradSesStatus
    ++ (encodeUIntLE 1 message.fastMarketIndicator))))

def decode (bytes : List UInt8) : Option (ProductSummaryMessage × List UInt8) := do
  let (lastMsgSeqNumProcessed, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUIntLE 1 bytes
  let (tradSesStatus, bytes) ← decodeUIntLE 1 bytes
  let (fastMarketIndicator, bytes) ← decodeUIntLE 1 bytes
  pure ({ lastMsgSeqNumProcessed, tradingSessionId, tradingSessionSubId, tradSesStatus, fastMarketIndicator }, bytes)

@[simp] theorem encode_length (message : ProductSummaryMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ProductSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProductSummaryMessage) (rest : List UInt8) :
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

end ProductSummaryMessage

/-- Order Details: 32 bytes -/
structure OrderDetails where
  trdRegTsTimePriority : BitVec 64
  displayQty : BitVec 64
  side : BitVec 8
  pad7 : Alpha 7
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDetails

def encode (message : OrderDetails) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsTimePriority
    ++ (encodeUIntLE 8 message.displayQty
    ++ (encodeUIntLE 1 message.side
    ++ (Alpha.encode message.pad7
    ++ (encodeUIntLE 8 message.price))))

def decode (bytes : List UInt8) : Option (OrderDetails × List UInt8) := do
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ trdRegTsTimePriority, displayQty, side, pad7, price }, bytes)

@[simp] theorem encode_length (message : OrderDetails) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderDetails) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDetails) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderDetails

/-- Snapshot Order Message: 32 bytes -/
structure SnapshotOrderMessage where
  orderDetails : OrderDetails
  deriving DecidableEq, Repr

namespace SnapshotOrderMessage

def encode (message : SnapshotOrderMessage) : List UInt8 :=
  OrderDetails.encode message.orderDetails

def decode (bytes : List UInt8) : Option (SnapshotOrderMessage × List UInt8) := do
  let (orderDetails, bytes) ← OrderDetails.decode bytes
  pure ({ orderDetails }, bytes)

@[simp] theorem encode_length (message : SnapshotOrderMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [OrderDetails.encode_length]

theorem encode_length_pos (message : SnapshotOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [OrderDetails.decode_encode, some_bind]
  rfl

end SnapshotOrderMessage

/-- Md Instrument Entry Grp: 24 bytes -/
structure MdInstrumentEntryGrp where
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 64
  mdEntryType : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace MdInstrumentEntryGrp

def encode (message : MdInstrumentEntryGrp) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPx
    ++ (encodeUIntLE 8 message.mdEntrySize
    ++ (encodeUIntLE 1 message.mdEntryType
    ++ (Alpha.encode message.pad7)))

def decode (bytes : List UInt8) : Option (MdInstrumentEntryGrp × List UInt8) := do
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryType, bytes) ← decodeUIntLE 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ mdEntryPx, mdEntrySize, mdEntryType, pad7 }, bytes)

@[simp] theorem encode_length (message : MdInstrumentEntryGrp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MdInstrumentEntryGrp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MdInstrumentEntryGrp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MdInstrumentEntryGrp

/-- Instrument Summary Message: 408 bytes -/
structure InstrumentSummaryMessage where
  securityId : BitVec 64
  lastUpdateTime : BitVec 64
  trdRegTsExecutionTime : BitVec 64
  totNoOrders : BitVec 32
  securityStatus : BitVec 8
  securityTradingStatus : BitVec 8
  fastMarketIndicator : BitVec 8
  noMdEntries : BitVec 8
  tradeVolume : BitVec 64
  noOfTrades : BitVec 32
  pad4 : Alpha 4
  mdInstrumentEntryGrp : Exact 15 MdInstrumentEntryGrp
  deriving DecidableEq, Repr

namespace InstrumentSummaryMessage

def encode (message : InstrumentSummaryMessage) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastUpdateTime
    ++ (encodeUIntLE 8 message.trdRegTsExecutionTime
    ++ (encodeUIntLE 4 message.totNoOrders
    ++ (encodeUIntLE 1 message.securityStatus
    ++ (encodeUIntLE 1 message.securityTradingStatus
    ++ (encodeUIntLE 1 message.fastMarketIndicator
    ++ (encodeUIntLE 1 message.noMdEntries
    ++ (encodeUIntLE 8 message.tradeVolume
    ++ (encodeUIntLE 4 message.noOfTrades
    ++ (Alpha.encode message.pad4
    ++ (encodeMany MdInstrumentEntryGrp.encode message.mdInstrumentEntryGrp.val)))))))))))

def decode (bytes : List UInt8) : Option (InstrumentSummaryMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsExecutionTime, bytes) ← decodeUIntLE 8 bytes
  let (totNoOrders, bytes) ← decodeUIntLE 4 bytes
  let (securityStatus, bytes) ← decodeUIntLE 1 bytes
  let (securityTradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (fastMarketIndicator, bytes) ← decodeUIntLE 1 bytes
  let (noMdEntries, bytes) ← decodeUIntLE 1 bytes
  let (tradeVolume, bytes) ← decodeUIntLE 8 bytes
  let (noOfTrades, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (mdInstrumentEntryGrp_, bytes) ← decodeMany MdInstrumentEntryGrp.decode 15 bytes
  if fits_mdInstrumentEntryGrp : mdInstrumentEntryGrp_.length = 15 then
    pure ({ securityId, lastUpdateTime, trdRegTsExecutionTime, totNoOrders, securityStatus, securityTradingStatus, fastMarketIndicator, noMdEntries, tradeVolume, noOfTrades, pad4, mdInstrumentEntryGrp := ⟨mdInstrumentEntryGrp_, fits_mdInstrumentEntryGrp⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : InstrumentSummaryMessage) : (encode message).length = 408 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeMany_length_const MdInstrumentEntryGrp.encode 24 MdInstrumentEntryGrp.encode_length, message.mdInstrumentEntryGrp.length_eq]

theorem encode_length_pos (message : InstrumentSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentSummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_exact 15 MdInstrumentEntryGrp.encode MdInstrumentEntryGrp.decode MdInstrumentEntryGrp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.mdInstrumentEntryGrp.length_eq]
  rfl

end InstrumentSummaryMessage

/-- Auction Best Bid Offer Message: 32 bytes -/
structure AuctionBestBidOfferMessage where
  transactTime : BitVec 64
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  deriving DecidableEq, Repr

namespace AuctionBestBidOfferMessage

def encode (message : AuctionBestBidOfferMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerPx)))

def decode (bytes : List UInt8) : Option (AuctionBestBidOfferMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, securityId, bidPx, offerPx }, bytes)

@[simp] theorem encode_length (message : AuctionBestBidOfferMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AuctionBestBidOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionBestBidOfferMessage) (rest : List UInt8) :
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

end AuctionBestBidOfferMessage

/-- Auction Clearing Price Message: 32 bytes -/
structure AuctionClearingPriceMessage where
  transactTime : BitVec 64
  securityId : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 64
  deriving DecidableEq, Repr

namespace AuctionClearingPriceMessage

def encode (message : AuctionClearingPriceMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.lastQty)))

def decode (bytes : List UInt8) : Option (AuctionClearingPriceMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, securityId, lastPx, lastQty }, bytes)

@[simp] theorem encode_length (message : AuctionClearingPriceMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AuctionClearingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionClearingPriceMessage) (rest : List UInt8) :
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

end AuctionClearingPriceMessage

/-- Top Of Book Message: 32 bytes -/
structure TopOfBookMessage where
  transactTime : BitVec 64
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  deriving DecidableEq, Repr

namespace TopOfBookMessage

def encode (message : TopOfBookMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerPx)))

def decode (bytes : List UInt8) : Option (TopOfBookMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, securityId, bidPx, offerPx }, bytes)

@[simp] theorem encode_length (message : TopOfBookMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TopOfBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfBookMessage) (rest : List UInt8) :
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

end TopOfBookMessage

/-- Order Add Message: 48 bytes -/
structure OrderAddMessage where
  trdRegTsTimeIn : BitVec 64
  securityId : BitVec 64
  orderDetails : OrderDetails
  deriving DecidableEq, Repr

namespace OrderAddMessage

def encode (message : OrderAddMessage) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsTimeIn
    ++ (encodeUIntLE 8 message.securityId
    ++ (OrderDetails.encode message.orderDetails))

def decode (bytes : List UInt8) : Option (OrderAddMessage × List UInt8) := do
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderDetails, bytes) ← OrderDetails.decode bytes
  pure ({ trdRegTsTimeIn, securityId, orderDetails }, bytes)

@[simp] theorem encode_length (message : OrderAddMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderDetails.encode_length]

theorem encode_length_pos (message : OrderAddMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [OrderDetails.decode_encode, some_bind]
  rfl

end OrderAddMessage

/-- Order Modify Message: 72 bytes -/
structure OrderModifyMessage where
  trdRegTsTimeIn : BitVec 64
  trdRegTsPrevTimePriority : BitVec 64
  prevPrice : BitVec 64
  prevDisplayQty : BitVec 64
  securityId : BitVec 64
  orderDetails : OrderDetails
  deriving DecidableEq, Repr

namespace OrderModifyMessage

def encode (message : OrderModifyMessage) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsTimeIn
    ++ (encodeUIntLE 8 message.trdRegTsPrevTimePriority
    ++ (encodeUIntLE 8 message.prevPrice
    ++ (encodeUIntLE 8 message.prevDisplayQty
    ++ (encodeUIntLE 8 message.securityId
    ++ (OrderDetails.encode message.orderDetails)))))

def decode (bytes : List UInt8) : Option (OrderModifyMessage × List UInt8) := do
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsPrevTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (prevPrice, bytes) ← decodeUIntLE 8 bytes
  let (prevDisplayQty, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderDetails, bytes) ← OrderDetails.decode bytes
  pure ({ trdRegTsTimeIn, trdRegTsPrevTimePriority, prevPrice, prevDisplayQty, securityId, orderDetails }, bytes)

@[simp] theorem encode_length (message : OrderModifyMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderDetails.encode_length]

theorem encode_length_pos (message : OrderModifyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyMessage) (rest : List UInt8) :
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
  rw [OrderDetails.decode_encode, some_bind]
  rfl

end OrderModifyMessage

/-- Order Modify Same Priority Message: 64 bytes -/
structure OrderModifySamePriorityMessage where
  trdRegTsTimeIn : BitVec 64
  transactTime : BitVec 64
  prevDisplayQty : BitVec 64
  securityId : BitVec 64
  orderDetails : OrderDetails
  deriving DecidableEq, Repr

namespace OrderModifySamePriorityMessage

def encode (message : OrderModifySamePriorityMessage) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsTimeIn
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.prevDisplayQty
    ++ (encodeUIntLE 8 message.securityId
    ++ (OrderDetails.encode message.orderDetails))))

def decode (bytes : List UInt8) : Option (OrderModifySamePriorityMessage × List UInt8) := do
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (prevDisplayQty, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderDetails, bytes) ← OrderDetails.decode bytes
  pure ({ trdRegTsTimeIn, transactTime, prevDisplayQty, securityId, orderDetails }, bytes)

@[simp] theorem encode_length (message : OrderModifySamePriorityMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderDetails.encode_length]

theorem encode_length_pos (message : OrderModifySamePriorityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifySamePriorityMessage) (rest : List UInt8) :
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
  rw [OrderDetails.decode_encode, some_bind]
  rfl

end OrderModifySamePriorityMessage

/-- Order Delete Message: 56 bytes -/
structure OrderDeleteMessage where
  trdRegTsTimeIn : BitVec 64
  transactTime : BitVec 64
  securityId : BitVec 64
  orderDetails : OrderDetails
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsTimeIn
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.securityId
    ++ (OrderDetails.encode message.orderDetails)))

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderDetails, bytes) ← OrderDetails.decode bytes
  pure ({ trdRegTsTimeIn, transactTime, securityId, orderDetails }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderDetails.encode_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [OrderDetails.decode_encode, some_bind]
  rfl

end OrderDeleteMessage

/-- Order Mass Delete Message: 16 bytes -/
structure OrderMassDeleteMessage where
  securityId : BitVec 64
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace OrderMassDeleteMessage

def encode (message : OrderMassDeleteMessage) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.transactTime)

def decode (bytes : List UInt8) : Option (OrderMassDeleteMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, transactTime }, bytes)

@[simp] theorem encode_length (message : OrderMassDeleteMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderMassDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderMassDeleteMessage

/-- Partial Order Execution Message: 56 bytes -/
structure PartialOrderExecutionMessage where
  side : BitVec 8
  pad7 : Alpha 7
  price : BitVec 64
  trdRegTsTimePriority : BitVec 64
  securityId : BitVec 64
  trdMatchId : BitVec 32
  pad4 : Alpha 4
  lastQty : BitVec 64
  lastPx : BitVec 64
  deriving DecidableEq, Repr

namespace PartialOrderExecutionMessage

def encode (message : PartialOrderExecutionMessage) : List UInt8 :=
  encodeUIntLE 1 message.side
    ++ (Alpha.encode message.pad7
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.trdRegTsTimePriority
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (Alpha.encode message.pad4
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 8 message.lastPx))))))))

def decode (bytes : List UInt8) : Option (PartialOrderExecutionMessage × List UInt8) := do
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  pure ({ side, pad7, price, trdRegTsTimePriority, securityId, trdMatchId, pad4, lastQty, lastPx }, bytes)

@[simp] theorem encode_length (message : PartialOrderExecutionMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : PartialOrderExecutionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartialOrderExecutionMessage) (rest : List UInt8) :
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

end PartialOrderExecutionMessage

/-- Full Order Execution Message: 56 bytes -/
structure FullOrderExecutionMessage where
  side : BitVec 8
  pad7 : Alpha 7
  price : BitVec 64
  trdRegTsTimePriority : BitVec 64
  securityId : BitVec 64
  trdMatchId : BitVec 32
  pad4 : Alpha 4
  lastQty : BitVec 64
  lastPx : BitVec 64
  deriving DecidableEq, Repr

namespace FullOrderExecutionMessage

def encode (message : FullOrderExecutionMessage) : List UInt8 :=
  encodeUIntLE 1 message.side
    ++ (Alpha.encode message.pad7
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.trdRegTsTimePriority
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (Alpha.encode message.pad4
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 8 message.lastPx))))))))

def decode (bytes : List UInt8) : Option (FullOrderExecutionMessage × List UInt8) := do
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  pure ({ side, pad7, price, trdRegTsTimePriority, securityId, trdMatchId, pad4, lastQty, lastPx }, bytes)

@[simp] theorem encode_length (message : FullOrderExecutionMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : FullOrderExecutionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FullOrderExecutionMessage) (rest : List UInt8) :
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

end FullOrderExecutionMessage

/-- Md Trade Entry Grp: 24 bytes -/
structure MdTradeEntryGrp where
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 64
  mdEntryType : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace MdTradeEntryGrp

def encode (message : MdTradeEntryGrp) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPx
    ++ (encodeUIntLE 8 message.mdEntrySize
    ++ (encodeUIntLE 1 message.mdEntryType
    ++ (Alpha.encode message.pad7)))

def decode (bytes : List UInt8) : Option (MdTradeEntryGrp × List UInt8) := do
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryType, bytes) ← decodeUIntLE 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ mdEntryPx, mdEntrySize, mdEntryType, pad7 }, bytes)

@[simp] theorem encode_length (message : MdTradeEntryGrp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MdTradeEntryGrp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MdTradeEntryGrp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MdTradeEntryGrp

/-- Trade Reversal Message: 416 bytes -/
structure TradeReversalMessage where
  securityId : BitVec 64
  transactTime : BitVec 64
  trdMatchId : BitVec 32
  pad4 : Alpha 4
  lastQty : BitVec 64
  lastPx : BitVec 64
  trdRegTsExecutionTime : BitVec 64
  noMdEntries : BitVec 8
  pad7 : Alpha 7
  mdTradeEntryGrp : Exact 15 MdTradeEntryGrp
  deriving DecidableEq, Repr

namespace TradeReversalMessage

def encode (message : TradeReversalMessage) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (Alpha.encode message.pad4
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.trdRegTsExecutionTime
    ++ (encodeUIntLE 1 message.noMdEntries
    ++ (Alpha.encode message.pad7
    ++ (encodeMany MdTradeEntryGrp.encode message.mdTradeEntryGrp.val)))))))))

def decode (bytes : List UInt8) : Option (TradeReversalMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsExecutionTime, bytes) ← decodeUIntLE 8 bytes
  let (noMdEntries, bytes) ← decodeUIntLE 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (mdTradeEntryGrp_, bytes) ← decodeMany MdTradeEntryGrp.decode 15 bytes
  if fits_mdTradeEntryGrp : mdTradeEntryGrp_.length = 15 then
    pure ({ securityId, transactTime, trdMatchId, pad4, lastQty, lastPx, trdRegTsExecutionTime, noMdEntries, pad7, mdTradeEntryGrp := ⟨mdTradeEntryGrp_, fits_mdTradeEntryGrp⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : TradeReversalMessage) : (encode message).length = 416 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeMany_length_const MdTradeEntryGrp.encode 24 MdTradeEntryGrp.encode_length, message.mdTradeEntryGrp.length_eq]

theorem encode_length_pos (message : TradeReversalMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReversalMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_exact 15 MdTradeEntryGrp.encode MdTradeEntryGrp.decode MdTradeEntryGrp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.mdTradeEntryGrp.length_eq]
  rfl

end TradeReversalMessage

/-- Execution Summary Message: 56 bytes -/
structure ExecutionSummaryMessage where
  securityId : BitVec 64
  aggressorTimestamp : BitVec 64
  execId : BitVec 64
  lastQty : BitVec 64
  aggressorSide : BitVec 8
  tradeCondition : BitVec 8
  pad6 : Alpha 6
  lastPx : BitVec 64
  restingHiddenQty : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionSummaryMessage

def encode (message : ExecutionSummaryMessage) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.aggressorTimestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 1 message.aggressorSide
    ++ (encodeUIntLE 1 message.tradeCondition
    ++ (Alpha.encode message.pad6
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.restingHiddenQty))))))))

def decode (bytes : List UInt8) : Option (ExecutionSummaryMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (aggressorTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (aggressorSide, bytes) ← decodeUIntLE 1 bytes
  let (tradeCondition, bytes) ← decodeUIntLE 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (restingHiddenQty, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, aggressorTimestamp, execId, lastQty, aggressorSide, tradeCondition, pad6, lastPx, restingHiddenQty }, bytes)

@[simp] theorem encode_length (message : ExecutionSummaryMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ExecutionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionSummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExecutionSummaryMessage

/-- Instrument Info Message: 40 bytes -/
structure InstrumentInfoMessage where
  securityId : BitVec 64
  closePrice : BitVec 64
  prevClosePrice : BitVec 64
  upperCktLimit : BitVec 64
  lowerCktLimit : BitVec 64
  deriving DecidableEq, Repr

namespace InstrumentInfoMessage

def encode (message : InstrumentInfoMessage) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.closePrice
    ++ (encodeUIntLE 8 message.prevClosePrice
    ++ (encodeUIntLE 8 message.upperCktLimit
    ++ (encodeUIntLE 8 message.lowerCktLimit))))

def decode (bytes : List UInt8) : Option (InstrumentInfoMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (closePrice, bytes) ← decodeUIntLE 8 bytes
  let (prevClosePrice, bytes) ← decodeUIntLE 8 bytes
  let (upperCktLimit, bytes) ← decodeUIntLE 8 bytes
  let (lowerCktLimit, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, closePrice, prevClosePrice, upperCktLimit, lowerCktLimit }, bytes)

@[simp] theorem encode_length (message : InstrumentInfoMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : InstrumentInfoMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentInfoMessage) (rest : List UInt8) :
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

end InstrumentInfoMessage

/-- Lpp Range Message: 24 bytes -/
structure LppRangeMessage where
  securityId : BitVec 64
  upperExecLimit : BitVec 64
  lowerExecLimit : BitVec 64
  deriving DecidableEq, Repr

namespace LppRangeMessage

def encode (message : LppRangeMessage) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.upperExecLimit
    ++ (encodeUIntLE 8 message.lowerExecLimit))

def decode (bytes : List UInt8) : Option (LppRangeMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (upperExecLimit, bytes) ← decodeUIntLE 8 bytes
  let (lowerExecLimit, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, upperExecLimit, lowerExecLimit }, bytes)

@[simp] theorem encode_length (message : LppRangeMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LppRangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LppRangeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LppRangeMessage

/-- Product State Change Message: 16 bytes -/
structure ProductStateChangeMessage where
  tradingSessionId : BitVec 8
  tradingSessionSubId : BitVec 8
  tradSesStatus : BitVec 8
  fastMarketIndicator : BitVec 8
  pad4 : Alpha 4
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace ProductStateChangeMessage

def encode (message : ProductStateChangeMessage) : List UInt8 :=
  encodeUIntLE 1 message.tradingSessionId
    ++ (encodeUIntLE 1 message.tradingSessionSubId
    ++ (encodeUIntLE 1 message.tradSesStatus
    ++ (encodeUIntLE 1 message.fastMarketIndicator
    ++ (Alpha.encode message.pad4
    ++ (encodeUIntLE 8 message.transactTime)))))

def decode (bytes : List UInt8) : Option (ProductStateChangeMessage × List UInt8) := do
  let (tradingSessionId, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUIntLE 1 bytes
  let (tradSesStatus, bytes) ← decodeUIntLE 1 bytes
  let (fastMarketIndicator, bytes) ← decodeUIntLE 1 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ tradingSessionId, tradingSessionSubId, tradSesStatus, fastMarketIndicator, pad4, transactTime }, bytes)

@[simp] theorem encode_length (message : ProductStateChangeMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ProductStateChangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProductStateChangeMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ProductStateChangeMessage

/-- Instrument State Change Message: 24 bytes -/
structure InstrumentStateChangeMessage where
  securityId : BitVec 64
  securityStatus : BitVec 8
  securityTradingStatus : BitVec 8
  fastMarketIndicator : BitVec 8
  pad5 : Alpha 5
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace InstrumentStateChangeMessage

def encode (message : InstrumentStateChangeMessage) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.securityStatus
    ++ (encodeUIntLE 1 message.securityTradingStatus
    ++ (encodeUIntLE 1 message.fastMarketIndicator
    ++ (Alpha.encode message.pad5
    ++ (encodeUIntLE 8 message.transactTime)))))

def decode (bytes : List UInt8) : Option (InstrumentStateChangeMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (securityStatus, bytes) ← decodeUIntLE 1 bytes
  let (securityTradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (fastMarketIndicator, bytes) ← decodeUIntLE 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, securityStatus, securityTradingStatus, fastMarketIndicator, pad5, transactTime }, bytes)

@[simp] theorem encode_length (message : InstrumentStateChangeMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentStateChangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentStateChangeMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InstrumentStateChangeMessage

/-- Instrmt Leg Grp: 16 bytes -/
structure InstrmtLegGrp where
  legSecurityId : BitVec 64
  legRatioQty : BitVec 32
  legSide : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace InstrmtLegGrp

def encode (message : InstrmtLegGrp) : List UInt8 :=
  encodeUIntLE 8 message.legSecurityId
    ++ (encodeUIntLE 4 message.legRatioQty
    ++ (encodeUIntLE 1 message.legSide
    ++ (Alpha.encode message.pad3)))

def decode (bytes : List UInt8) : Option (InstrmtLegGrp × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUIntLE 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ legSecurityId, legRatioQty, legSide, pad3 }, bytes)

@[simp] theorem encode_length (message : InstrmtLegGrp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrmtLegGrp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrmtLegGrp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrmtLegGrp

/-- Add Complex Instrument Message: 104 bytes -/
structure AddComplexInstrumentMessage where
  securityId : BitVec 64
  transactTime : BitVec 64
  securitySubType : BitVec 32
  productComplex : BitVec 8
  impliedMarketIndicator : BitVec 8
  noLegs : BitVec 8
  pad1 : Alpha 1
  instrmtLegGrp : Exact 5 InstrmtLegGrp
  deriving DecidableEq, Repr

namespace AddComplexInstrumentMessage

def encode (message : AddComplexInstrumentMessage) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.securitySubType
    ++ (encodeUIntLE 1 message.productComplex
    ++ (encodeUIntLE 1 message.impliedMarketIndicator
    ++ (encodeUIntLE 1 message.noLegs
    ++ (Alpha.encode message.pad1
    ++ (encodeMany InstrmtLegGrp.encode message.instrmtLegGrp.val)))))))

def decode (bytes : List UInt8) : Option (AddComplexInstrumentMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securitySubType, bytes) ← decodeUIntLE 4 bytes
  let (productComplex, bytes) ← decodeUIntLE 1 bytes
  let (impliedMarketIndicator, bytes) ← decodeUIntLE 1 bytes
  let (noLegs, bytes) ← decodeUIntLE 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (instrmtLegGrp_, bytes) ← decodeMany InstrmtLegGrp.decode 5 bytes
  if fits_instrmtLegGrp : instrmtLegGrp_.length = 5 then
    pure ({ securityId, transactTime, securitySubType, productComplex, impliedMarketIndicator, noLegs, pad1, instrmtLegGrp := ⟨instrmtLegGrp_, fits_instrmtLegGrp⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : AddComplexInstrumentMessage) : (encode message).length = 104 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeMany_length_const InstrmtLegGrp.encode 16 InstrmtLegGrp.encode_length, message.instrmtLegGrp.length_eq]

theorem encode_length_pos (message : AddComplexInstrumentMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddComplexInstrumentMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_exact 5 InstrmtLegGrp.encode InstrmtLegGrp.decode InstrmtLegGrp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.instrmtLegGrp.length_eq]
  rfl

end AddComplexInstrumentMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | heartbeatMessage (message : HeartbeatMessage) -- 13001
  | productSummaryMessage (message : ProductSummaryMessage) -- 13600
  | snapshotOrderMessage (message : SnapshotOrderMessage) -- 13602
  | instrumentSummaryMessage (message : InstrumentSummaryMessage) -- 13601
  | auctionBestBidOfferMessage (message : AuctionBestBidOfferMessage) -- 13500
  | auctionClearingPriceMessage (message : AuctionClearingPriceMessage) -- 13501
  | topOfBookMessage (message : TopOfBookMessage) -- 13504
  | orderAddMessage (message : OrderAddMessage) -- 13100
  | orderModifyMessage (message : OrderModifyMessage) -- 13101
  | orderModifySamePriorityMessage (message : OrderModifySamePriorityMessage) -- 13106
  | orderDeleteMessage (message : OrderDeleteMessage) -- 13102
  | orderMassDeleteMessage (message : OrderMassDeleteMessage) -- 13103
  | partialOrderExecutionMessage (message : PartialOrderExecutionMessage) -- 13105
  | fullOrderExecutionMessage (message : FullOrderExecutionMessage) -- 13104
  | tradeReversalMessage (message : TradeReversalMessage) -- 13200
  | executionSummaryMessage (message : ExecutionSummaryMessage) -- 13202
  | instrumentInfoMessage (message : InstrumentInfoMessage) -- 13203
  | lppRangeMessage (message : LppRangeMessage) -- 13204
  | productStateChangeMessage (message : ProductStateChangeMessage) -- 13300
  | instrumentStateChangeMessage (message : InstrumentStateChangeMessage) -- 13301
  | addComplexInstrumentMessage (message : AddComplexInstrumentMessage) -- 13400
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .heartbeatMessage _ => 13001
  | .productSummaryMessage _ => 13600
  | .snapshotOrderMessage _ => 13602
  | .instrumentSummaryMessage _ => 13601
  | .auctionBestBidOfferMessage _ => 13500
  | .auctionClearingPriceMessage _ => 13501
  | .topOfBookMessage _ => 13504
  | .orderAddMessage _ => 13100
  | .orderModifyMessage _ => 13101
  | .orderModifySamePriorityMessage _ => 13106
  | .orderDeleteMessage _ => 13102
  | .orderMassDeleteMessage _ => 13103
  | .partialOrderExecutionMessage _ => 13105
  | .fullOrderExecutionMessage _ => 13104
  | .tradeReversalMessage _ => 13200
  | .executionSummaryMessage _ => 13202
  | .instrumentInfoMessage _ => 13203
  | .lppRangeMessage _ => 13204
  | .productStateChangeMessage _ => 13300
  | .instrumentStateChangeMessage _ => 13301
  | .addComplexInstrumentMessage _ => 13400

def encode : Payload → List UInt8
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .productSummaryMessage message => ProductSummaryMessage.encode message
  | .snapshotOrderMessage message => SnapshotOrderMessage.encode message
  | .instrumentSummaryMessage message => InstrumentSummaryMessage.encode message
  | .auctionBestBidOfferMessage message => AuctionBestBidOfferMessage.encode message
  | .auctionClearingPriceMessage message => AuctionClearingPriceMessage.encode message
  | .topOfBookMessage message => TopOfBookMessage.encode message
  | .orderAddMessage message => OrderAddMessage.encode message
  | .orderModifyMessage message => OrderModifyMessage.encode message
  | .orderModifySamePriorityMessage message => OrderModifySamePriorityMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderMassDeleteMessage message => OrderMassDeleteMessage.encode message
  | .partialOrderExecutionMessage message => PartialOrderExecutionMessage.encode message
  | .fullOrderExecutionMessage message => FullOrderExecutionMessage.encode message
  | .tradeReversalMessage message => TradeReversalMessage.encode message
  | .executionSummaryMessage message => ExecutionSummaryMessage.encode message
  | .instrumentInfoMessage message => InstrumentInfoMessage.encode message
  | .lppRangeMessage message => LppRangeMessage.encode message
  | .productStateChangeMessage message => ProductStateChangeMessage.encode message
  | .instrumentStateChangeMessage message => InstrumentStateChangeMessage.encode message
  | .addComplexInstrumentMessage message => AddComplexInstrumentMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 416 := by
  cases message with
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | productSummaryMessage inner =>
    simp only [encode, ProductSummaryMessage.encode_length]
    omega
  | snapshotOrderMessage inner =>
    simp only [encode, SnapshotOrderMessage.encode_length]
    omega
  | instrumentSummaryMessage inner =>
    simp only [encode, InstrumentSummaryMessage.encode_length]
    omega
  | auctionBestBidOfferMessage inner =>
    simp only [encode, AuctionBestBidOfferMessage.encode_length]
    omega
  | auctionClearingPriceMessage inner =>
    simp only [encode, AuctionClearingPriceMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [encode, TopOfBookMessage.encode_length]
    omega
  | orderAddMessage inner =>
    simp only [encode, OrderAddMessage.encode_length]
    omega
  | orderModifyMessage inner =>
    simp only [encode, OrderModifyMessage.encode_length]
    omega
  | orderModifySamePriorityMessage inner =>
    simp only [encode, OrderModifySamePriorityMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [encode, OrderDeleteMessage.encode_length]
    omega
  | orderMassDeleteMessage inner =>
    simp only [encode, OrderMassDeleteMessage.encode_length]
    omega
  | partialOrderExecutionMessage inner =>
    simp only [encode, PartialOrderExecutionMessage.encode_length]
    omega
  | fullOrderExecutionMessage inner =>
    simp only [encode, FullOrderExecutionMessage.encode_length]
    omega
  | tradeReversalMessage inner =>
    simp only [encode, TradeReversalMessage.encode_length]
    omega
  | executionSummaryMessage inner =>
    simp only [encode, ExecutionSummaryMessage.encode_length]
    omega
  | instrumentInfoMessage inner =>
    simp only [encode, InstrumentInfoMessage.encode_length]
    omega
  | lppRangeMessage inner =>
    simp only [encode, LppRangeMessage.encode_length]
    omega
  | productStateChangeMessage inner =>
    simp only [encode, ProductStateChangeMessage.encode_length]
    omega
  | instrumentStateChangeMessage inner =>
    simp only [encode, InstrumentStateChangeMessage.encode_length]
    omega
  | addComplexInstrumentMessage inner =>
    simp only [encode, AddComplexInstrumentMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 13001 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 13600 then (ProductSummaryMessage.decode bytes).map fun (message, rest) => (.productSummaryMessage message, rest)
  else if tag = 13602 then (SnapshotOrderMessage.decode bytes).map fun (message, rest) => (.snapshotOrderMessage message, rest)
  else if tag = 13601 then (InstrumentSummaryMessage.decode bytes).map fun (message, rest) => (.instrumentSummaryMessage message, rest)
  else if tag = 13500 then (AuctionBestBidOfferMessage.decode bytes).map fun (message, rest) => (.auctionBestBidOfferMessage message, rest)
  else if tag = 13501 then (AuctionClearingPriceMessage.decode bytes).map fun (message, rest) => (.auctionClearingPriceMessage message, rest)
  else if tag = 13504 then (TopOfBookMessage.decode bytes).map fun (message, rest) => (.topOfBookMessage message, rest)
  else if tag = 13100 then (OrderAddMessage.decode bytes).map fun (message, rest) => (.orderAddMessage message, rest)
  else if tag = 13101 then (OrderModifyMessage.decode bytes).map fun (message, rest) => (.orderModifyMessage message, rest)
  else if tag = 13106 then (OrderModifySamePriorityMessage.decode bytes).map fun (message, rest) => (.orderModifySamePriorityMessage message, rest)
  else if tag = 13102 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 13103 then (OrderMassDeleteMessage.decode bytes).map fun (message, rest) => (.orderMassDeleteMessage message, rest)
  else if tag = 13105 then (PartialOrderExecutionMessage.decode bytes).map fun (message, rest) => (.partialOrderExecutionMessage message, rest)
  else if tag = 13104 then (FullOrderExecutionMessage.decode bytes).map fun (message, rest) => (.fullOrderExecutionMessage message, rest)
  else if tag = 13200 then (TradeReversalMessage.decode bytes).map fun (message, rest) => (.tradeReversalMessage message, rest)
  else if tag = 13202 then (ExecutionSummaryMessage.decode bytes).map fun (message, rest) => (.executionSummaryMessage message, rest)
  else if tag = 13203 then (InstrumentInfoMessage.decode bytes).map fun (message, rest) => (.instrumentInfoMessage message, rest)
  else if tag = 13204 then (LppRangeMessage.decode bytes).map fun (message, rest) => (.lppRangeMessage message, rest)
  else if tag = 13300 then (ProductStateChangeMessage.decode bytes).map fun (message, rest) => (.productStateChangeMessage message, rest)
  else if tag = 13301 then (InstrumentStateChangeMessage.decode bytes).map fun (message, rest) => (.instrumentStateChangeMessage message, rest)
  else if tag = 13400 then (AddComplexInstrumentMessage.decode bytes).map fun (message, rest) => (.addComplexInstrumentMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  msgSeqNum : BitVec 32
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 4 message.msgSeqNum
    ++ (Payload.encode message.payload))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ msgSeqNum, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, HeartbeatMessage.encode_length]
    omega
  | productSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ProductSummaryMessage.encode_length]
    omega
  | snapshotOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SnapshotOrderMessage.encode_length]
    omega
  | instrumentSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentSummaryMessage.encode_length]
    omega
  | auctionBestBidOfferMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AuctionBestBidOfferMessage.encode_length]
    omega
  | auctionClearingPriceMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AuctionClearingPriceMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TopOfBookMessage.encode_length]
    omega
  | orderAddMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderAddMessage.encode_length]
    omega
  | orderModifyMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderModifyMessage.encode_length]
    omega
  | orderModifySamePriorityMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderModifySamePriorityMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderDeleteMessage.encode_length]
    omega
  | orderMassDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderMassDeleteMessage.encode_length]
    omega
  | partialOrderExecutionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, PartialOrderExecutionMessage.encode_length]
    omega
  | fullOrderExecutionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, FullOrderExecutionMessage.encode_length]
    omega
  | tradeReversalMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeReversalMessage.encode_length]
    omega
  | executionSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ExecutionSummaryMessage.encode_length]
    omega
  | instrumentInfoMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentInfoMessage.encode_length]
    omega
  | lppRangeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LppRangeMessage.encode_length]
    omega
  | productStateChangeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ProductStateChangeMessage.encode_length]
    omega
  | instrumentStateChangeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentStateChangeMessage.encode_length]
    omega
  | addComplexInstrumentMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AddComplexInstrumentMessage.encode_length]
    omega

/-- Size rule: Body Len counts the bytes after it plus 2, so it is written from the body and checked on decode -/
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
  packetHeader : PacketHeader
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  PacketHeader.encode message.packetHeader
    ++ (encodeMany Message.encode message.message)

def decode (bytes : List UInt8) : Option Packet := do
  let (packetHeader, bytes) ← PacketHeader.decode bytes
  let message ← decodeAll Message.decode bytes.length bytes
  pure { packetHeader, message }

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [PacketHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [PacketHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end Packet

end Omi.BseBseindiaEobiFbeV14
