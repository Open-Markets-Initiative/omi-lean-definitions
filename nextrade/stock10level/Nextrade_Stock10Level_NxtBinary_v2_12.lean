import Wire

/-!
# Nextrade Nextrade Stock Market Data 10 Level v2.12

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NextradeNextradeStock10levelNxtbinaryV212

/-- Polling Data Message: 8 bytes -/
structure PollingDataMessage where
  currentTime1MinuteInterval : Alpha 4
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace PollingDataMessage

def encode (message : PollingDataMessage) : List UInt8 :=
  Alpha.encode message.currentTime1MinuteInterval
    ++ (encodeUIntLE 4 message.endKeyword)

def decode (bytes : List UInt8) : Option (PollingDataMessage × List UInt8) := do
  let (currentTime1MinuteInterval, bytes) ← Alpha.decode 4 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ currentTime1MinuteInterval, endKeyword }, bytes)

@[simp] theorem encode_length (message : PollingDataMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : PollingDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PollingDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end PollingDataMessage

/-- Securities Quote 10 Level Message: 416 bytes -/
structure SecuritiesQuote10LevelMessage where
  messageSequenceNumber : BitVec 32
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  processingTimeOfTradingSystem : Alpha 12
  askLevel1Price : Alpha 8
  bidLevel1Price : Alpha 8
  askLevel1Volume : BitVec 64
  bidLevel1Volume : BitVec 64
  askLevel2Price : Alpha 8
  bidLevel2Price : Alpha 8
  askLevel2Volume : BitVec 64
  bidLevel2Volume : BitVec 64
  askLevel3Price : Alpha 8
  bidLevel3Price : Alpha 8
  askLevel3Volume : BitVec 64
  bidLevel3Volume : BitVec 64
  askLevel4Price : Alpha 8
  bidLevel4Price : Alpha 8
  askLevel4Volume : BitVec 64
  bidLevel4Volume : BitVec 64
  askLevel5Price : Alpha 8
  bidLevel5Price : Alpha 8
  askLevel5Volume : BitVec 64
  bidLevel5Volume : BitVec 64
  askLevel6Price : Alpha 8
  bidLevel6Price : Alpha 8
  askLevel6Volume : BitVec 64
  bidLevel6Volume : BitVec 64
  askLevel7Price : Alpha 8
  bidLevel7Price : Alpha 8
  askLevel7Volume : BitVec 64
  bidLevel7Volume : BitVec 64
  askLevel8Price : Alpha 8
  bidLevel8Price : Alpha 8
  askLevel8Volume : BitVec 64
  bidLevel8Volume : BitVec 64
  askLevel9Price : Alpha 8
  bidLevel9Price : Alpha 8
  askLevel9Volume : BitVec 64
  bidLevel9Volume : BitVec 64
  askLevel10Price : Alpha 8
  bidLevel10Price : Alpha 8
  askLevel10Volume : BitVec 64
  bidLevel10Volume : BitVec 64
  totalAskVolume : BitVec 64
  totalBidVolume : BitVec 64
  estimatedTradingPrice : Alpha 8
  estimatedTradingVolume : BitVec 64
  midPrice : Alpha 8
  totalMidPriceAskVolumeTotalAskVolumeOnMidPrice : BitVec 64
  totalMidPriceBidVolumeTotalBidVolumeOnMidPrice : BitVec 64
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace SecuritiesQuote10LevelMessage

def encode (message : SecuritiesQuote10LevelMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.askLevel1Price
    ++ (Alpha.encode message.bidLevel1Price
    ++ (encodeUIntLE 8 message.askLevel1Volume
    ++ (encodeUIntLE 8 message.bidLevel1Volume
    ++ (Alpha.encode message.askLevel2Price
    ++ (Alpha.encode message.bidLevel2Price
    ++ (encodeUIntLE 8 message.askLevel2Volume
    ++ (encodeUIntLE 8 message.bidLevel2Volume
    ++ (Alpha.encode message.askLevel3Price
    ++ (Alpha.encode message.bidLevel3Price
    ++ (encodeUIntLE 8 message.askLevel3Volume
    ++ (encodeUIntLE 8 message.bidLevel3Volume
    ++ (Alpha.encode message.askLevel4Price
    ++ (Alpha.encode message.bidLevel4Price
    ++ (encodeUIntLE 8 message.askLevel4Volume
    ++ (encodeUIntLE 8 message.bidLevel4Volume
    ++ (Alpha.encode message.askLevel5Price
    ++ (Alpha.encode message.bidLevel5Price
    ++ (encodeUIntLE 8 message.askLevel5Volume
    ++ (encodeUIntLE 8 message.bidLevel5Volume
    ++ (Alpha.encode message.askLevel6Price
    ++ (Alpha.encode message.bidLevel6Price
    ++ (encodeUIntLE 8 message.askLevel6Volume
    ++ (encodeUIntLE 8 message.bidLevel6Volume
    ++ (Alpha.encode message.askLevel7Price
    ++ (Alpha.encode message.bidLevel7Price
    ++ (encodeUIntLE 8 message.askLevel7Volume
    ++ (encodeUIntLE 8 message.bidLevel7Volume
    ++ (Alpha.encode message.askLevel8Price
    ++ (Alpha.encode message.bidLevel8Price
    ++ (encodeUIntLE 8 message.askLevel8Volume
    ++ (encodeUIntLE 8 message.bidLevel8Volume
    ++ (Alpha.encode message.askLevel9Price
    ++ (Alpha.encode message.bidLevel9Price
    ++ (encodeUIntLE 8 message.askLevel9Volume
    ++ (encodeUIntLE 8 message.bidLevel9Volume
    ++ (Alpha.encode message.askLevel10Price
    ++ (Alpha.encode message.bidLevel10Price
    ++ (encodeUIntLE 8 message.askLevel10Volume
    ++ (encodeUIntLE 8 message.bidLevel10Volume
    ++ (encodeUIntLE 8 message.totalAskVolume
    ++ (encodeUIntLE 8 message.totalBidVolume
    ++ (Alpha.encode message.estimatedTradingPrice
    ++ (encodeUIntLE 8 message.estimatedTradingVolume
    ++ (Alpha.encode message.midPrice
    ++ (encodeUIntLE 8 message.totalMidPriceAskVolumeTotalAskVolumeOnMidPrice
    ++ (encodeUIntLE 8 message.totalMidPriceBidVolumeTotalBidVolumeOnMidPrice
    ++ (encodeUIntLE 4 message.endKeyword)))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecuritiesQuote10LevelMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (askLevel1Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel1Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel1Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel1Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel2Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel2Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel2Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel2Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel3Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel3Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel3Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel3Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel4Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel4Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel4Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel4Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel5Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel5Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel5Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel5Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel6Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel6Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel6Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel6Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel7Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel7Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel7Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel7Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel8Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel8Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel8Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel8Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel9Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel9Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel9Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel9Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel10Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel10Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel10Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel10Volume, bytes) ← decodeUIntLE 8 bytes
  let (totalAskVolume, bytes) ← decodeUIntLE 8 bytes
  let (totalBidVolume, bytes) ← decodeUIntLE 8 bytes
  let (estimatedTradingPrice, bytes) ← Alpha.decode 8 bytes
  let (estimatedTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (midPrice, bytes) ← Alpha.decode 8 bytes
  let (totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, bytes) ← decodeUIntLE 8 bytes
  let (totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, bytes) ← decodeUIntLE 8 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, askLevel1Price, bidLevel1Price, askLevel1Volume, bidLevel1Volume, askLevel2Price, bidLevel2Price, askLevel2Volume, bidLevel2Volume, askLevel3Price, bidLevel3Price, askLevel3Volume, bidLevel3Volume, askLevel4Price, bidLevel4Price, askLevel4Volume, bidLevel4Volume, askLevel5Price, bidLevel5Price, askLevel5Volume, bidLevel5Volume, askLevel6Price, bidLevel6Price, askLevel6Volume, bidLevel6Volume, askLevel7Price, bidLevel7Price, askLevel7Volume, bidLevel7Volume, askLevel8Price, bidLevel8Price, askLevel8Volume, bidLevel8Volume, askLevel9Price, bidLevel9Price, askLevel9Volume, bidLevel9Volume, askLevel10Price, bidLevel10Price, askLevel10Volume, bidLevel10Volume, totalAskVolume, totalBidVolume, estimatedTradingPrice, estimatedTradingVolume, midPrice, totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, endKeyword }, bytes)

@[simp] theorem encode_length (message : SecuritiesQuote10LevelMessage) : (encode message).length = 416 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SecuritiesQuote10LevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecuritiesQuote10LevelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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

end SecuritiesQuote10LevelMessage

/-- Securities Order Filled Message: 138 bytes -/
structure SecuritiesOrderFilledMessage where
  messageSequenceNumber : BitVec 32
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  processingTimeOfTradingSystem : Alpha 12
  priceChangeAgainstPreviousDay : Alpha 1
  aPriceChangeAgainstThePreviousDay : Alpha 8
  tradingPrice : Alpha 8
  tradingVolume : BitVec 64
  openingPrice : Alpha 8
  todaysHigh : Alpha 8
  todaysLow : Alpha 8
  accumulatedTradingVolume : BitVec 64
  accumulatedTradingValue : Alpha 16
  finalAskBidTypeCode : Alpha 1
  lpHoldingQuantity : BitVec 64
  theBestAsk : Alpha 8
  theBestBid : Alpha 8
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace SecuritiesOrderFilledMessage

def encode (message : SecuritiesOrderFilledMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.priceChangeAgainstPreviousDay
    ++ (Alpha.encode message.aPriceChangeAgainstThePreviousDay
    ++ (Alpha.encode message.tradingPrice
    ++ (encodeUIntLE 8 message.tradingVolume
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.todaysHigh
    ++ (Alpha.encode message.todaysLow
    ++ (encodeUIntLE 8 message.accumulatedTradingVolume
    ++ (Alpha.encode message.accumulatedTradingValue
    ++ (Alpha.encode message.finalAskBidTypeCode
    ++ (encodeUIntLE 8 message.lpHoldingQuantity
    ++ (Alpha.encode message.theBestAsk
    ++ (Alpha.encode message.theBestBid
    ++ (encodeUIntLE 4 message.endKeyword)))))))))))))))))))

def decode (bytes : List UInt8) : Option (SecuritiesOrderFilledMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (priceChangeAgainstPreviousDay, bytes) ← Alpha.decode 1 bytes
  let (aPriceChangeAgainstThePreviousDay, bytes) ← Alpha.decode 8 bytes
  let (tradingPrice, bytes) ← Alpha.decode 8 bytes
  let (tradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (openingPrice, bytes) ← Alpha.decode 8 bytes
  let (todaysHigh, bytes) ← Alpha.decode 8 bytes
  let (todaysLow, bytes) ← Alpha.decode 8 bytes
  let (accumulatedTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (accumulatedTradingValue, bytes) ← Alpha.decode 16 bytes
  let (finalAskBidTypeCode, bytes) ← Alpha.decode 1 bytes
  let (lpHoldingQuantity, bytes) ← decodeUIntLE 8 bytes
  let (theBestAsk, bytes) ← Alpha.decode 8 bytes
  let (theBestBid, bytes) ← Alpha.decode 8 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, priceChangeAgainstPreviousDay, aPriceChangeAgainstThePreviousDay, tradingPrice, tradingVolume, openingPrice, todaysHigh, todaysLow, accumulatedTradingVolume, accumulatedTradingValue, finalAskBidTypeCode, lpHoldingQuantity, theBestAsk, theBestBid, endKeyword }, bytes)

@[simp] theorem encode_length (message : SecuritiesOrderFilledMessage) : (encode message).length = 138 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SecuritiesOrderFilledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecuritiesOrderFilledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecuritiesOrderFilledMessage

/-- Market Operation Ts Message: 59 bytes -/
structure MarketOperationTsMessage where
  messageSequenceNumber : BitVec 32
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  processingTimeOfTradingSystem : Alpha 12
  boardEventId : Alpha 3
  startTimeOfABoardEvent : Alpha 9
  boardEventGroupCode : BitVec 32
  tradingHaltReasonCode : Alpha 3
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace MarketOperationTsMessage

def encode (message : MarketOperationTsMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.boardEventId
    ++ (Alpha.encode message.startTimeOfABoardEvent
    ++ (encodeUIntLE 4 message.boardEventGroupCode
    ++ (Alpha.encode message.tradingHaltReasonCode
    ++ (encodeUIntLE 4 message.endKeyword))))))))))

def decode (bytes : List UInt8) : Option (MarketOperationTsMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (boardEventId, bytes) ← Alpha.decode 3 bytes
  let (startTimeOfABoardEvent, bytes) ← Alpha.decode 9 bytes
  let (boardEventGroupCode, bytes) ← decodeUIntLE 4 bytes
  let (tradingHaltReasonCode, bytes) ← Alpha.decode 3 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, boardEventId, startTimeOfABoardEvent, boardEventGroupCode, tradingHaltReasonCode, endKeyword }, bytes)

@[simp] theorem encode_length (message : MarketOperationTsMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketOperationTsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketOperationTsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketOperationTsMessage

/-- Issue Closing Message: 83 bytes -/
structure IssueClosingMessage where
  messageSequenceNumber : BitVec 32
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  closingPrice : Alpha 8
  closingPriceTypeCode : Alpha 1
  upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession : Alpha 8
  lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession : Alpha 8
  closingPriceWeightedStockPriceAverage : Alpha 8
  closingPriceBasePriceOfBuyIn : Alpha 8
  closingPriceUpperLimitOfBuyIn : Alpha 8
  closingPriceLowerLimitOfBuyIn : Alpha 8
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace IssueClosingMessage

def encode (message : IssueClosingMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.closingPrice
    ++ (Alpha.encode message.closingPriceTypeCode
    ++ (Alpha.encode message.upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession
    ++ (Alpha.encode message.lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession
    ++ (Alpha.encode message.closingPriceWeightedStockPriceAverage
    ++ (Alpha.encode message.closingPriceBasePriceOfBuyIn
    ++ (Alpha.encode message.closingPriceUpperLimitOfBuyIn
    ++ (Alpha.encode message.closingPriceLowerLimitOfBuyIn
    ++ (encodeUIntLE 4 message.endKeyword))))))))))))

def decode (bytes : List UInt8) : Option (IssueClosingMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (closingPrice, bytes) ← Alpha.decode 8 bytes
  let (closingPriceTypeCode, bytes) ← Alpha.decode 1 bytes
  let (upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, bytes) ← Alpha.decode 8 bytes
  let (lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, bytes) ← Alpha.decode 8 bytes
  let (closingPriceWeightedStockPriceAverage, bytes) ← Alpha.decode 8 bytes
  let (closingPriceBasePriceOfBuyIn, bytes) ← Alpha.decode 8 bytes
  let (closingPriceUpperLimitOfBuyIn, bytes) ← Alpha.decode 8 bytes
  let (closingPriceLowerLimitOfBuyIn, bytes) ← Alpha.decode 8 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, closingPrice, closingPriceTypeCode, upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, closingPriceWeightedStockPriceAverage, closingPriceBasePriceOfBuyIn, closingPriceUpperLimitOfBuyIn, closingPriceLowerLimitOfBuyIn, endKeyword }, bytes)

@[simp] theorem encode_length (message : IssueClosingMessage) : (encode message).length = 83 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : IssueClosingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueClosingMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IssueClosingMessage

/-- Triggering Removing Vi Message: 89 bytes -/
structure TriggeringRemovingViMessage where
  messageSequenceNumber : BitVec 32
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  processingTimeOfTradingSystem : Alpha 12
  theTimeEndingVi : Alpha 9
  viStatusCode : Alpha 1
  viTypeCode : Alpha 1
  aBasePriceToTriggerStaticVi : Alpha 8
  aBasePriceToTriggerDynamicVi : Alpha 8
  viTriggeringPrice : Alpha 8
  disparateRatioToTriggerStaticVi : Alpha 8
  disparateRatioToTriggerDynamicVi : Alpha 8
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace TriggeringRemovingViMessage

def encode (message : TriggeringRemovingViMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.theTimeEndingVi
    ++ (Alpha.encode message.viStatusCode
    ++ (Alpha.encode message.viTypeCode
    ++ (Alpha.encode message.aBasePriceToTriggerStaticVi
    ++ (Alpha.encode message.aBasePriceToTriggerDynamicVi
    ++ (Alpha.encode message.viTriggeringPrice
    ++ (Alpha.encode message.disparateRatioToTriggerStaticVi
    ++ (Alpha.encode message.disparateRatioToTriggerDynamicVi
    ++ (encodeUIntLE 4 message.endKeyword)))))))))))))

def decode (bytes : List UInt8) : Option (TriggeringRemovingViMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (theTimeEndingVi, bytes) ← Alpha.decode 9 bytes
  let (viStatusCode, bytes) ← Alpha.decode 1 bytes
  let (viTypeCode, bytes) ← Alpha.decode 1 bytes
  let (aBasePriceToTriggerStaticVi, bytes) ← Alpha.decode 8 bytes
  let (aBasePriceToTriggerDynamicVi, bytes) ← Alpha.decode 8 bytes
  let (viTriggeringPrice, bytes) ← Alpha.decode 8 bytes
  let (disparateRatioToTriggerStaticVi, bytes) ← Alpha.decode 8 bytes
  let (disparateRatioToTriggerDynamicVi, bytes) ← Alpha.decode 8 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, theTimeEndingVi, viStatusCode, viTypeCode, aBasePriceToTriggerStaticVi, aBasePriceToTriggerDynamicVi, viTriggeringPrice, disparateRatioToTriggerStaticVi, disparateRatioToTriggerDynamicVi, endKeyword }, bytes)

@[simp] theorem encode_length (message : TriggeringRemovingViMessage) : (encode message).length = 89 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TriggeringRemovingViMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TriggeringRemovingViMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TriggeringRemovingViMessage

/-- Closing Price Trading Quote Message: 42 bytes -/
structure ClosingPriceTradingQuoteMessage where
  messageSequenceNumber : BitVec 32
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  totalAskVolume : BitVec 64
  totalBidVolume : BitVec 64
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace ClosingPriceTradingQuoteMessage

def encode (message : ClosingPriceTradingQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (encodeUIntLE 8 message.totalAskVolume
    ++ (encodeUIntLE 8 message.totalBidVolume
    ++ (encodeUIntLE 4 message.endKeyword))))))

def decode (bytes : List UInt8) : Option (ClosingPriceTradingQuoteMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (totalAskVolume, bytes) ← decodeUIntLE 8 bytes
  let (totalBidVolume, bytes) ← decodeUIntLE 8 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, totalAskVolume, totalBidVolume, endKeyword }, bytes)

@[simp] theorem encode_length (message : ClosingPriceTradingQuoteMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ClosingPriceTradingQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClosingPriceTradingQuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ClosingPriceTradingQuoteMessage

/-- Any Payload, selected by TR Code -/
inductive Payload where
  | pollingDataMessage (message : PollingDataMessage) -- "I2500" 0x4932353030
  | securitiesQuote10LevelMessage (message : SecuritiesQuote10LevelMessage) -- "B651S" 0x4236353153
  | securitiesQuote10LevelMessage284377297233 (message : SecuritiesQuote10LevelMessage) -- "B651Q" 0x4236353151
  | securitiesOrderFilledMessage (message : SecuritiesOrderFilledMessage) -- "A351S" 0x4133353153
  | securitiesOrderFilledMessage280031998289 (message : SecuritiesOrderFilledMessage) -- "A351Q" 0x4133353151
  | marketOperationTsMessage (message : MarketOperationTsMessage) -- "A751S" 0x4137353153
  | marketOperationTsMessage280099107153 (message : MarketOperationTsMessage) -- "A751Q" 0x4137353151
  | issueClosingMessage (message : IssueClosingMessage) -- "A651S" 0x4136353153
  | issueClosingMessage280082329937 (message : IssueClosingMessage) -- "A651Q" 0x4136353151
  | triggeringRemovingViMessage (message : TriggeringRemovingViMessage) -- "R851S" 0x5238353153
  | triggeringRemovingViMessage353130328401 (message : TriggeringRemovingViMessage) -- "R851Q" 0x5238353151
  | closingPriceTradingQuoteMessage (message : ClosingPriceTradingQuoteMessage) -- "E151S" 0x4531353153
  | closingPriceTradingQuoteMessage297178313041 (message : ClosingPriceTradingQuoteMessage) -- "E151Q" 0x4531353151
  deriving DecidableEq, Repr

namespace Payload

/-- The TR Code each message is sent under -/
def tag : Payload → BitVec 40
  | .pollingDataMessage _ => 314374959152
  | .securitiesQuote10LevelMessage _ => 284377297235
  | .securitiesQuote10LevelMessage284377297233 _ => 284377297233
  | .securitiesOrderFilledMessage _ => 280031998291
  | .securitiesOrderFilledMessage280031998289 _ => 280031998289
  | .marketOperationTsMessage _ => 280099107155
  | .marketOperationTsMessage280099107153 _ => 280099107153
  | .issueClosingMessage _ => 280082329939
  | .issueClosingMessage280082329937 _ => 280082329937
  | .triggeringRemovingViMessage _ => 353130328403
  | .triggeringRemovingViMessage353130328401 _ => 353130328401
  | .closingPriceTradingQuoteMessage _ => 297178313043
  | .closingPriceTradingQuoteMessage297178313041 _ => 297178313041

def encode : Payload → List UInt8
  | .pollingDataMessage message => PollingDataMessage.encode message
  | .securitiesQuote10LevelMessage message => SecuritiesQuote10LevelMessage.encode message
  | .securitiesQuote10LevelMessage284377297233 message => SecuritiesQuote10LevelMessage.encode message
  | .securitiesOrderFilledMessage message => SecuritiesOrderFilledMessage.encode message
  | .securitiesOrderFilledMessage280031998289 message => SecuritiesOrderFilledMessage.encode message
  | .marketOperationTsMessage message => MarketOperationTsMessage.encode message
  | .marketOperationTsMessage280099107153 message => MarketOperationTsMessage.encode message
  | .issueClosingMessage message => IssueClosingMessage.encode message
  | .issueClosingMessage280082329937 message => IssueClosingMessage.encode message
  | .triggeringRemovingViMessage message => TriggeringRemovingViMessage.encode message
  | .triggeringRemovingViMessage353130328401 message => TriggeringRemovingViMessage.encode message
  | .closingPriceTradingQuoteMessage message => ClosingPriceTradingQuoteMessage.encode message
  | .closingPriceTradingQuoteMessage297178313041 message => ClosingPriceTradingQuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 416 := by
  cases message with
  | pollingDataMessage inner =>
    simp only [encode, PollingDataMessage.encode_length]
    omega
  | securitiesQuote10LevelMessage inner =>
    simp only [encode, SecuritiesQuote10LevelMessage.encode_length]
    omega
  | securitiesQuote10LevelMessage284377297233 inner =>
    simp only [encode, SecuritiesQuote10LevelMessage.encode_length]
    omega
  | securitiesOrderFilledMessage inner =>
    simp only [encode, SecuritiesOrderFilledMessage.encode_length]
    omega
  | securitiesOrderFilledMessage280031998289 inner =>
    simp only [encode, SecuritiesOrderFilledMessage.encode_length]
    omega
  | marketOperationTsMessage inner =>
    simp only [encode, MarketOperationTsMessage.encode_length]
    omega
  | marketOperationTsMessage280099107153 inner =>
    simp only [encode, MarketOperationTsMessage.encode_length]
    omega
  | issueClosingMessage inner =>
    simp only [encode, IssueClosingMessage.encode_length]
    omega
  | issueClosingMessage280082329937 inner =>
    simp only [encode, IssueClosingMessage.encode_length]
    omega
  | triggeringRemovingViMessage inner =>
    simp only [encode, TriggeringRemovingViMessage.encode_length]
    omega
  | triggeringRemovingViMessage353130328401 inner =>
    simp only [encode, TriggeringRemovingViMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage inner =>
    simp only [encode, ClosingPriceTradingQuoteMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage297178313041 inner =>
    simp only [encode, ClosingPriceTradingQuoteMessage.encode_length]
    omega

def decode (tag : BitVec 40) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 314374959152 then (PollingDataMessage.decode bytes).map fun (message, rest) => (.pollingDataMessage message, rest)
  else if tag = 284377297235 then (SecuritiesQuote10LevelMessage.decode bytes).map fun (message, rest) => (.securitiesQuote10LevelMessage message, rest)
  else if tag = 284377297233 then (SecuritiesQuote10LevelMessage.decode bytes).map fun (message, rest) => (.securitiesQuote10LevelMessage284377297233 message, rest)
  else if tag = 280031998291 then (SecuritiesOrderFilledMessage.decode bytes).map fun (message, rest) => (.securitiesOrderFilledMessage message, rest)
  else if tag = 280031998289 then (SecuritiesOrderFilledMessage.decode bytes).map fun (message, rest) => (.securitiesOrderFilledMessage280031998289 message, rest)
  else if tag = 280099107155 then (MarketOperationTsMessage.decode bytes).map fun (message, rest) => (.marketOperationTsMessage message, rest)
  else if tag = 280099107153 then (MarketOperationTsMessage.decode bytes).map fun (message, rest) => (.marketOperationTsMessage280099107153 message, rest)
  else if tag = 280082329939 then (IssueClosingMessage.decode bytes).map fun (message, rest) => (.issueClosingMessage message, rest)
  else if tag = 280082329937 then (IssueClosingMessage.decode bytes).map fun (message, rest) => (.issueClosingMessage280082329937 message, rest)
  else if tag = 353130328403 then (TriggeringRemovingViMessage.decode bytes).map fun (message, rest) => (.triggeringRemovingViMessage message, rest)
  else if tag = 353130328401 then (TriggeringRemovingViMessage.decode bytes).map fun (message, rest) => (.triggeringRemovingViMessage353130328401 message, rest)
  else if tag = 297178313043 then (ClosingPriceTradingQuoteMessage.decode bytes).map fun (message, rest) => (.closingPriceTradingQuoteMessage message, rest)
  else if tag = 297178313041 then (ClosingPriceTradingQuoteMessage.decode bytes).map fun (message, rest) => (.closingPriceTradingQuoteMessage297178313041 message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Packet -/
structure Packet where
  payload : Payload
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 5 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (trCode, bytes) ← decodeUInt 5 bytes
  let (payload, bytes) ← Payload.decode trCode bytes
  pure ({ payload }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 421 := by
  unfold encode
  cases message.payload with
  | pollingDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PollingDataMessage.encode_length]
    omega
  | securitiesQuote10LevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesQuote10LevelMessage.encode_length]
    omega
  | securitiesQuote10LevelMessage284377297233 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesQuote10LevelMessage.encode_length]
    omega
  | securitiesOrderFilledMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesOrderFilledMessage.encode_length]
    omega
  | securitiesOrderFilledMessage280031998289 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesOrderFilledMessage.encode_length]
    omega
  | marketOperationTsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationTsMessage.encode_length]
    omega
  | marketOperationTsMessage280099107153 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationTsMessage.encode_length]
    omega
  | issueClosingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueClosingMessage.encode_length]
    omega
  | issueClosingMessage280082329937 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueClosingMessage.encode_length]
    omega
  | triggeringRemovingViMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TriggeringRemovingViMessage.encode_length]
    omega
  | triggeringRemovingViMessage353130328401 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TriggeringRemovingViMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ClosingPriceTradingQuoteMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage297178313041 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ClosingPriceTradingQuoteMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Packet

end Omi.NextradeNextradeStock10levelNxtbinaryV212
