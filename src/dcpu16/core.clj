(ns dcpu16.core)

;;; TODO: fix interaction between POP and JSR

(defonce op-mask (int 0xF))
(defonce op-val-mask (int 0x3F))
(defonce alt-op-mask (int 0x3F))
(defonce reg-mask (int 0x7))
(defonce mem-mask (int 0xFFFF))
(defonce lit-mask (int 0x1F))
(defonce skiptable (int-array 0x20))
(aset-int skiptable 0x10 1)
(aset-int skiptable 0x11 1)
(aset-int skiptable 0x12 1)
(aset-int skiptable 0x13 1)
(aset-int skiptable 0x14 1)
(aset-int skiptable 0x15 1)
(aset-int skiptable 0x16 1)
(aset-int skiptable 0x17 1)
(aset-int skiptable 0x1E 1)
(aset-int skiptable 0x1F 1)
(def ^:dynamic *dcpu* {:r (int-array 8 0)
                       :pc (int 0)
                       :sp (int 0xFFFF)
                       :ov (int 0)
                       :m (int-array 65536 0)
                       :l (int-array (range 0x00 0x20))
                       :op nil
                       :a nil
                       :b nil})

(defn program-load [dcpu words]
  (doseq [[idx val] (map list (range (count words)) words)]
    (aset ^ints (:m dcpu) (int idx) (int val))))

(defn reg [dcpu oprnd r] (assoc dcpu oprnd [:r r]))
(defn reg-pointer [dcpu oprnd p] (assoc dcpu oprnd [:m (aget (:r dcpu) (bit-and reg-mask p))]))
(defn next-word-reg-pointer [dcpu oprnd p]
  (assoc dcpu
    oprnd [:m (bit-and mem-mask (+ (aget (:r dcpu) (bit-and p reg-mask))
                                   (aget (:m dcpu) (:pc dcpu))))]
    :pc (int (inc (:pc dcpu)))))
(defn spop [dcpu oprnd] (assoc dcpu
                          oprnd [:m (:sp dcpu)]
                          :sp (int (inc (:sp dcpu)))))
(defn speek [dcpu oprnd] (assoc dcpu oprnd [:m (:sp dcpu)]))
(defn spush [dcpu oprnd]
  (let [sp (int (dec (:sp dcpu)))]
    (assoc dcpu oprnd [:m sp] :sp sp)))
(defn sp [dcpu oprnd] (assoc dcpu oprnd [:sp]))
(defn pc [dcpu oprnd] (assoc dcpu oprnd [:pc]))
(defn ov [dcpu oprnd] (assoc dcpu oprnd [:ov]))
(defn next-word-pointer [dcpu oprnd] (assoc dcpu
                                       oprnd [:m (aget (:m dcpu) (:pc dcpu))]
                                       :pc (int (inc (:pc dcpu)))))
(defn next-word-literal [dcpu oprnd] (assoc dcpu
                                       oprnd [:m (:pc dcpu)]
                                       :pc (int (inc (:pc dcpu)))))
(defn literal-val [dcpu oprnd code] (assoc dcpu
                                      oprnd [:l (bit-and code lit-mask)]))
(defn opr [dcpu oprnd code]
  (case code
    (0x00 0x01 0x02 0x03 0x04 0x05 0x06 0x07) (reg dcpu oprnd code)
    (0x08 0x09 0x0a 0x0b 0x0c 0x0d 0x0e 0x0f) (reg-pointer dcpu oprnd code)
    (0x10 0x11 0x12 0x13 0x14 0x15 0x16 0x17) (next-word-reg-pointer dcpu oprnd code)
    (0x18) (spop dcpu oprnd)
    (0x19) (speek dcpu oprnd)
    (0x1a) (spush dcpu oprnd)
    (0x1b) (sp dcpu oprnd)
    (0x1c) (pc dcpu oprnd)
    (0x1d) (ov dcpu oprnd)
    (0x1e) (next-word-pointer dcpu oprnd)
    (0x1f) (next-word-literal dcpu oprnd)
    (literal-val dcpu oprnd code)))

(defn mem-load [dcpu oprnd]
  (let [[loc n] oprnd]
    (if n (aget (dcpu loc) n)
        (dcpu loc))))
(defn mem-store [dcpu oprnd val]
  (let [[loc n] oprnd
        masked-val (bit-and val mem-mask)]
    (if n (do (aset-int (dcpu loc) n masked-val)
              dcpu)
        (assoc dcpu loc masked-val))))

(defn set [dcpu a b]
  (mem-store dcpu a (mem-load dcpu b)))
(defn add [dcpu a b]
  (let [res (+ (mem-load dcpu a) (mem-load dcpu b))]
    (-> dcpu
        (mem-store a res)
        (mem-store [:ov] (if (>= (bit-shift-right res 16) 0x1) 0x0001 0x0)))))
(defn sub [dcpu a b]
  (let [res (- (mem-load dcpu a) (mem-load dcpu b))]
    (-> dcpu
        (mem-store a res)
        (mem-store [:ov] (if (< res 0) 0xFFFF 0x0)))))
(defn mul [dcpu a b]
  (let [res (* (mem-load dcpu a) (mem-load dcpu b))]
    (-> dcpu
        (mem-store a res)
        (mem-store [:ov] (bit-and (bit-shift-right res 16) mem-mask)))))
(defn div [dcpu a b]
  (let [aval (mem-load dcpu a)
        bval (mem-load dcpu b)]
    (if (= bval 0)
      (-> dcpu
          (mem-store a 0x0)
          (mem-store [:ov] 0x0))
      (let [res (/ aval bval)]
        (-> dcpu
            (mem-store a res)
            (mem-store [:ov] (bit-and (/ (bit-shift-left aval 16) bval) mem-mask)))))))
(defn mod [dcpu a b]
  (let [aval (mem-load dcpu a)
        bval (mem-load dcpu b)]
    (if (= bval 0)
      (mem-store dcpu a 0x0)
      (mem-store dcpu a (clojure.core/mod aval bval)))))
(defn shl [dcpu a b]
  (let [aval (mem-load dcpu a)
        bval (mem-load dcpu b)
        res (bit-shift-left aval bval)
        ov (bit-and (bit-shift-right res 16) mem-mask)]
    (-> dcpu
        (mem-store a res)
        (mem-store [:ov] ov))))
(defn shr [dcpu a b]
  (let [aval (mem-load dcpu a)
        bval (mem-load dcpu b)
        res (bit-shift-right aval bval)
        ov (bit-and (bit-shift-right (bit-shift-left aval 16) bval) mem-mask)]
    (-> dcpu
        (mem-store a res)
        (mem-store [:ov] ov))))
(defn and [dcpu a b]
  (let [aval (mem-load dcpu a)
        bval (mem-load dcpu b)
        res (bit-and a b)]
    (mem-store dcpu a res)))
(defn bor [dcpu a b]
  (let [aval (mem-load dcpu a)
        bval (mem-load dcpu b)
        res (bit-or a b)]
    (mem-store dcpu a res)))
(defn xor [dcpu a b]
  (let [aval (mem-load dcpu a)
        bval (mem-load dcpu b)
        res (bit-xor a b)]
    (mem-store dcpu a res)))

(defn skip [dcpu]
  (let [op (aget (:m dcpu) (:pc dcpu))]
    (assoc dcpu :pc (int (+ 1 (:pc dcpu)
                            (aget skiptable (bit-shift-right op 10))
                            (if (= (bit-and op op-mask) 0)
                              (aget skiptable (bit-and (bit-shift-right op 4) 0x1F))
                              0))))))

(defn ife [dcpu a b]
  (let [aval (mem-load dcpu a)
        bval (mem-load dcpu b)]
    (if (not= aval bval) (skip dcpu) dcpu)))
(defn ifn [dcpu a b]
  (let [aval (mem-load dcpu a)
        bval (mem-load dcpu b)]
    (if (= aval bval) (skip dcpu) dcpu)))
(defn ifg [dcpu a b]
  (let [aval (mem-load dcpu a)
        bval (mem-load dcpu b)]
    (if (<= aval bval) (skip dcpu) dcpu)))
(defn ifb [dcpu a b]
  (let [aval (mem-load dcpu a)
        bval (mem-load dcpu b)]
    (if (= (bit-and aval bval) 0) (skip dcpu) dcpu)))

(defn jsr [dcpu a]
  (let [spval (dec (mem-load dcpu [:sp]))
        pcval (mem-load dcpu [:pc])
        aval (mem-load dcpu a)]
    (prn (map #(format "%04x" %) [spval pcval aval]))
    (-> dcpu
        (mem-store [:m spval] pcval)
        (mem-store [:sp] spval)
        (mem-store [:pc] aval))))

(defn step [dcpu]
  (let [op (aget (:m dcpu) (:pc dcpu))
        dcpu (assoc dcpu :pc (int (inc (:pc dcpu))))]
    (if (not= 0 (bit-and op op-mask))
      (let [dest (bit-and (bit-shift-right op 4) op-val-mask)
            dcpu (opr (opr dcpu :a dest) :b (bit-shift-right op 10))
            a (:a dcpu)
            b (:b dcpu)]
        (condp = (bit-and op op-mask)
          0x1 (set dcpu a b)
          0x2 (add dcpu a b)
          0x3 (sub dcpu a b)
          0x4 (mul dcpu a b)
          0x5 (div dcpu a b)
          0x6 (mod dcpu a b)
          0x7 (shl dcpu a b)
          0x8 (shr dcpu a b)
          0x9 (and dcpu a b)
          0xa (bor dcpu a b)
          0xb (xor dcpu a b)
          0xc (ife dcpu a b)
          0xd (ifn dcpu a b)
          0xe (ifn dcpu a b)
          0xf (ifn dcpu a b)))
      (let [alt-op (bit-and (bit-shift-right op 4) alt-op-mask)
            dcpu (opr dcpu :a (bit-and (bit-shift-right op 10) op-val-mask))
            a (:a dcpu)]
        (condp = alt-op
          0x01 (jsr dcpu a)
          (format "Illegal opcode: 0x%x" alt-op))))))

(defn print-header []
  (do (prn "PC   SP   OV   A    B    C    X    Y    Z    I    J    Instruction")
      (prn "---- ---- ---- ---- ---- ---- ---- ---- ---- ---- ---- -----------")))

(defn print-dcpu [dcpu]
  (let [{:keys [pc sp ov r m]} dcpu]
    (prn (apply str (map #(format "%04x " %) [pc sp ov (aget r 0) (aget r 1) (aget r 2) (aget r 3) (aget r 4) (aget r 5) (aget r 6) (aget r 7) (aget m pc)])))))

(defn run-program [dcpu]
  (do (print-header)
      (print-dcpu dcpu)
      (loop [dcpu (step dcpu)]
        (if (map? dcpu)
          (do (print-dcpu dcpu)
              (recur (step dcpu)))
          dcpu))))

(comment
  (def prgm [0x7c01 0x0030 0x7de1 0x1000 0x0020 0x7803 0x1000 0xc00d
             0x7dc1 0x001a 0xa861 0x7c01 0x2000 0x2161 0x2000 0x8463
             0x806d 0x7dc1 0x000d 0x9031 0x7c10 0x0018 0x7dc1 0x001a
             0x9037 0x61c1 0x7dc1 0x001a 0x0000 0x0000 0x0000 0x0000]))
