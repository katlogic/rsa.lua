-- Example usage of lgmp

local print, setmetatable, io, string, math, assert, pairs, table, ipairs, unpack, tonumber
=     print, setmetatable, io, string, math, assert, pairs, table, ipairs, unpack, tonumber
local gmp = require('gmp')
local bn = gmp.z

local rsa = {}
local rsa_mt = {__index=rsa}
local BITS = 2048
local DEFAULT_EXP = 65537

---------------------------------------
-- rsa.* methods
---------------------------------------
do local _ENV = rsa

rsa_mt = rsa_mt
rnd = gmp.rand()

-- generate random prime
-- @bits - number of bits wanted (will be rounded down to step of 8)
-- returns: random prime between 1 .. 2^bits
function random_prime(bits)
  bits = bits
  return rnd:zbits(bits):nextprime()
end

-- pretty progress printer default writer
-- ... - strings to print, space separetd
function write(...)
  io.stdout:write(table.concat({...}, " "))
  io.stdout:flush()
end

-- pretty progress printer factory
-- @out - terminal writer
-- returns: function(step,nstep) to be passed to new_key
function pretty_cb(out)
  out = out or write
  return function(n,outof)
    if n == 0 then
      out("["..string.rep(".", outof).."]"..string.rep("\b", outof+1))
    elseif n < outof then
      out("*")
    elseif n == outof then
      out("] ")
    end
  end
end

-- generate new key
-- @bits - number of bits in modulus
-- @?exp - public exponent (default: 65537)
-- @?progress(step,nsteps) - called with step out of nsteps
-- return - rsa key
function new_key(bits,exp,progress)
  -- defaults
  bits = bits or DEFAULT_BITS
  exp = exp or DEFAULT_EXP 

  -- progres
  local counter = 0
  local cb = progress and function()
    if counter <= 7 then
      progress(counter,7)
    end
    counter = counter+1
  end or function() end

  -- generate prime number such that gcd(e,n-1) == 1
  local function rsa_prime(bits,e,cb)
    local r, r1
    cb()
    repeat
      r = rsa.random_prime(bits)
      cb()
      r1 = r-1
    until r1:gcd(e) == bn(1)
    return r, r1
  end

  cb()

  local e = bn(exp)
  local p, q, p1, q1, mod
  -- because nextprime monotonously increments,
  -- we might end up (very rarely) with larger than bits modulus
  repeat
    p, p1 = rsa_prime(bits/2, e, cb)
    q, q1 = rsa_prime(bits/2, e, cb)
    mod = p*q
    local realbits = mod:sizeinbase(2)
  until realbits < bits
  -- ensure p > q
  if p < q then p, p1, q, q1 = q, q1, p, p1 end
  -- phi
  local phi = p1 * q1
  -- calculate private exponent d
  cb()
  local d = assert(e:invert(phi))
  -- dmp1 = d mod (p-1)
  local dmp1 = d % p1
  local dmq1 = d % q1
  cb()
  local iqmp = assert(q:invert(p))
  cb()
  
  return setmetatable({
    pub = {
      e = e,
      mod = mod,
    },
    priv = {
      d = d,
      -- optional uncompressed key part
      p = p,
      q = q,
      dmp1 = dmp1,
      dmq1 = dmq1,
      iqmp = iqmp,
    }
  }, rsa_mt)
end
function export(self, pubonly)
  local k = self.pub.e:hex() .. '|' .. self.pub.mod:hex()
  if not pubonly then
    k = k .. '|' .. self.priv.d:hex() .. '|' .. self.priv.p:hex() .. '|' .. self.priv.q:hex() .. '|' ..
    self.priv.dmp1:hex() .. '|' .. self.priv.dmq1:hex() .. '|' .. self.priv.iqmp:hex()
  end
  return k
end

function import(s)
  local vals = {}
  local l =  { s:match('(%x+)|(%x+)|(%x+)|(%x+)|(%x+)|(%x+)|(%x+)|(%x+)') }
  if not l[1] then
    l = { s:match('(%x+)|(%x+)') }
  end
  for k,v in ipairs(l) do
    vals[k] = bn(v, 16)
  end
  local e,mod,d,p,q,dmp1,dmq1,iqmp = unpack(vals)
  return setmetatable({
    pub = {
      e = e,
      mod = mod,
    },
    priv = d and {
      d = d,
      -- optional uncompressed key part
      p = p,
      q = q,
      dmp1 = dmp1,
      dmq1 = dmq1,
      iqmp = iqmp,
    }
  }, rsa_mt)
end

-- Convert string buffer to GMP number
-- @s - bytes
-- return - gmp number
function to_n(s)
  return bn(s:gsub('(.)', function(c)
    return string.format("%02x", c:byte(1))
  end), 16)
end

-- Convert GMP number to string byffer
-- @n - gmp number
-- return - bytes
function to_s(n)
  local s = n:hex()
  -- pad to byte
  if #s % 2 == 1 then
    s = '0' .. s
  end
  return s:gsub('(..)', function(c)
    return string.char(tonumber(c, 16))
  end)
end

-- private operation (encrypt or sign)
-- @msg - pkcs
-- return - encrypted number
function do_private(self,msg)
  local pk = self.priv
  local p,q,dmp1,dmq1,iqmp = pk.p,pk.q,pk.dmp1,pk.dmq1,pk.iqmp
  -- no extended fields; do slow rsa
  if not (p and q and dmp1 and dmq1 and iqmp) then
    return msg:powm(self.priv.d, self.pub.mod)
  end
  -- fast rsa
  local vp, vq = msg % p, msg % q
  vp:powm(dmp1, p, vp)
  vq:powm(dmq1, q, vq)
  return (((vp - vq) * iqmp) % p) * q + vq
end

-- public operation (decrypt or verify)
-- @msg - number from do_private
-- return - decrypted pkcs
function do_public(self,msg)
  return msg:powm(self.pub.e, self.pub.mod)
end

-- pretty print rsa object
function rsa_mt.__tostring(self)
  local res = "RSA {\n  pub = {\n"
  for k,v in pairs(self.pub) do
    res = string.format("%s    %s = %s\n", res, k, v:hex())
  end
  res = res .."  }\n  priv = {\n"
  for k,v in pairs(self.priv) do
    res = string.format("%s    %s = %s\n", res, k, v:hex())
  end
  return res .. "  }\n}\n"
end

end -- _ENV = rsa

if not ... then
  rsa.write 'Generating new RSA key '
  k = rsa.new_key(2048,65537,rsa.pretty_cb())
  rsa.write 'Done\n'
  print(k)
  local e =  k:export()
  local epub =  k:export(true)
  local kpub = rsa.import(epub)
  local encrypted = rsa.to_s(kpub:do_public(rsa.to_n('blahblah')))
  assert(rsa.to_s(k:do_private(rsa.to_n(encrypted))) == 'blahblah')
  print('Crypt/decrypt passed')
end


return rsa

