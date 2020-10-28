\ forth hashtables by gustav melck, sep 2020
\ vim: fdm=marker

\ a hashtable's first cell is the count of remaining cells (i.e., its size)

s" inc/forth-list-tools.fs" required

private{ \ {{{

: gthrow  ( ior addr u -- )  2 pick  if  type ." ; forth-ht error " dup . cr throw  else  2drop drop  then  ;

: (zero-ht)  ( addr count in-loop? -- )
    if  r> drop  then  dup 0=  if  2drop  else  over 0 swap !  1- swap cell+ swap true recurse  then  ;
: zero-ht  ( ht -- )  dup @ swap cell+ swap false (zero-ht)  ;

: free-ht-list  ( list in-loop? -- )
    if  r> drop  then
    ?dup 0<>  if
        dup >r car@ car@ free s" free-ht-list error1" gthrow  q@ 0<>  if  r@ car@ cdr@ q@ execute  then
        r@ car@ free s" free-ht-list error2" gthrow  r> dup cdr@ swap free s" free-ht-list error3" gthrow
        true recurse
    then  ;
: (free-ht-contents)  ( addr count in-loop? q: xt -- )
    if  r> drop  then
    ?dup 0=  if  drop  else  over @ false free-ht-list  1- swap cell+ swap true recurse  then  ;

0 value ht              0 value ht0
0 value current-key     0 value current-hash        0 value kv-addr

: free-ht-key  ( -- )
    current-key 0<>  if  current-key free s" free-ht-key error1" gthrow  then  0 to current-key  ;

: (hash)  ( addr u1 hash in-loop? -- hash' )
    if  r> drop  then
    over 0=  if  nip nip  else  dup 5 lshift + 2 pick c@ xor ht @ mod >r  1- swap 1+ swap r> true recurse  then  ;
: hash  ( addr u -- u' )  5381 ht @ mod false (hash)  ;

: (lookup-kv-addr)  ( list-addr in-loop? -- addr' )
    if  r> drop  then
    dup 0<>  if
        dup >r car@ car@ count current-key count compare 0=  if  r> car@  else  r> cdr@ true recurse  then
    then  ;
: lookup-kv-addr  ( index -- addr )  cells ht0 + @ false (lookup-kv-addr)  ;

: make-cstring  ( addr u -- addr' )
    dup 1+ chars allocate s" make-cstring error1" gthrow >r  dup r@ c! r@ 1+ swap cmove  r>  ;

: print-kv  ( kv-cons -- )  dup car@ count type ." =>"  cdr@ . ." ; "  ;

: (print-ht)  ( addr counter in-loop? -- )
    if  r> drop  then
    ?dup 0=  if  drop  else
        over dup ." at " . ." : " @ ['] print-kv swap print-list cr  1- swap cell+ swap true recurse
    then  ;

0 value kv-xt

: (for-each-ht-kv-pair)  ( addr count in-loop? q: xt -- q: xt)
    if  r> drop  then
    ?dup 0=  if  drop  else
        >r >r  kv-xt r@ @ for-each-list-item  r> cell+ r> 1- true recurse
    then  ;

: free-ht-contents  ( xt ht -- )  swap >q dup @ swap cell+ swap false (free-ht-contents) q> drop  free-ht-key  ;

}private \ }}}

: make-ht  ( size -- ht )  dup 1+ cells allocate s" make-ht error1" gthrow dup >r !  r@ zero-ht  r>  ;
: free-ht  ( xt ht -- )  \ xt, if 0>, is called for each value in ht
    dup >r free-ht-contents  r> free s" free-ht error1" gthrow  ;

: allot-ht  ( size "name" -- )  create  here  swap dup 1+ cells allot  swap dup -rot !  zero-ht  ;
: clear-ht  ( xt ht -- )  dup >r free-ht-contents  r> zero-ht  ;  \ xt, if 0>, is called for each value in ht

: with-ht  ( ht -- )  dup to ht  cell+ to ht0  ;
: with-ht-key  ( addr u -- )
    free-ht-key  make-cstring dup to current-key  count hash dup to current-hash  lookup-kv-addr to kv-addr  ;
: ht-key-exists?  ( -- f )  kv-addr 0<>  ;
: ht@  ( -- item )  ht-key-exists?  if  kv-addr cdr@  else  0  then  ;
: ht!  ( item -- )
    ht-key-exists? 0=  if
        cons current-hash cells ht0 + dup >r @ +list  r@ !  r> @ car@ to kv-addr
        current-key count make-cstring kv-addr car!
    then  kv-addr cdr!  ;

: for-each-ht-kv-pair  ( xt -- )  to kv-xt  ht0 ht @ false (for-each-ht-kv-pair)  ;

: print-ht  ( -- ) ht0 ht @ false (print-ht)  ;

privatize

\ tests {{{
\ : test  ( -- )
\     29 make-ht dup >r with-ht
\     s" gustav" with-ht-key ht-key-exists? . ht@ . cr 10 ht!  ht-key-exists? . ht@ . cr  11 ht!
\     s" Marisa" with-ht-key 13 ht!
\     s" mArisa" with-ht-key 12 ht!
\     s" MArisa" with-ht-key ht@ . 14 ht!
\     s" Gustav" with-ht-key 99 ht!
\     s" hustav" with-ht-key 98 ht!
\     cr print-ht
\     0 r@ free-ht
\     r> drop
\     .s  ;
\ 
\ test
\ }}}

