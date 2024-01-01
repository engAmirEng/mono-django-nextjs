import fs from 'fs';
import querystring from 'querystring';
import OGCrypto from 'crypto';

// A type of promise-like that resolves synchronously and supports only one observer

// Converts argument to a function that always returns a Promise
function _async(f) {
  return function () {
    for (var args = [], i = 0; i < arguments.length; i++) {
      args[i] = arguments[i];
    }
    try {
      return Promise.resolve(f.apply(this, args));
    } catch (e) {
      return Promise.reject(e);
    }
  };
}

// Awaits on a value that may or may not be a Promise (equivalent to the await keyword in ES2015, with continuations passed explicitly)
function _await(value, then, direct) {
  if (direct) {
    return then ? then(value) : value;
  }
  if (!value || !value.then) {
    value = Promise.resolve(value);
  }
  return then ? value.then(then) : value;
}

// Awaits on a value that may or may not be a Promise, then ignores it
function _awaitIgnored(value, direct) {
  if (!direct) {
    return value && value.then ? value.then(_empty) : Promise.resolve();
  }
}

// Proceeds after a value has resolved, or proceeds immediately if the value is not thenable
function _continue(value, then) {
  return value && value.then ? value.then(then) : then(value);
}

// Proceeds after a value has resolved, or proceeds immediately if the value is not thenable
function _continueIgnored(value) {
  if (value && value.then) {
    return value.then(_empty);
  }
}
typeof Symbol !== "undefined" ? Symbol.iterator || (Symbol.iterator = Symbol("Symbol.iterator")) : "@@iterator";
typeof Symbol !== "undefined" ? Symbol.asyncIterator || (Symbol.asyncIterator = Symbol("Symbol.asyncIterator")) : "@@asyncIterator";

// Asynchronously call a function and pass the result to explicitly passed continuations
function _call(body, then, direct) {
  if (direct) {
    return then ? then(body()) : body();
  }
  try {
    var result = Promise.resolve(body());
    return then ? result.then(then) : result;
  } catch (e) {
    return Promise.reject(e);
  }
}

// Asynchronously call a function and pass the result to explicitly passed continuations
function _invoke(body, then) {
  var result = body();
  if (result && result.then) {
    return result.then(then);
  }
  return then(result);
}

// Asynchronously call a function and send errors to recovery continuation
function _catch(body, recover) {
  try {
    var result = body();
  } catch (e) {
    return recover(e);
  }
  if (result && result.then) {
    return result.then(void 0, recover);
  }
  return result;
}

// Asynchronously await a promise and pass the result to a finally continuation
function _finallyRethrows(body, finalizer) {
  try {
    var result = body();
  } catch (e) {
    return finalizer(true, e);
  }
  if (result && result.then) {
    return result.then(finalizer.bind(null, false), finalizer.bind(null, true));
  }
  return finalizer(false, result);
}

// Rethrow or return a value from a finally continuation
function _rethrow(thrown, value) {
  if (thrown) throw value;
  return value;
}

// Empty function to implement break and other control flow that ignores asynchronous results
function _empty() {}

/* eslint-disable no-fallthrough */
/* eslint-disable @typescript-eslint/explicit-module-boundary-types */
/**
 * this is from https://github.com/nginx/njs-examples/blob/master/njs/http/certs/js/x509.js
 *
 *
 */

function asn1_parse_oid(buf) {
  var oid = [];
  var sid = 0;
  var cur_octet = buf[0];
  if (cur_octet < 40) {
    oid.push(0);
    oid.push(cur_octet);
  } else if (cur_octet < 80) {
    oid.push(1);
    oid.push(cur_octet - 40);
  } else {
    oid.push(2);
    oid.push(cur_octet - 80);
  }
  for (var n = 1; n < buf.length; n++) {
    cur_octet = buf[n];
    if (cur_octet < 0x80) {
      sid += cur_octet;
      if (sid > Number.MAX_SAFE_INTEGER) throw 'Too big SID value: ' + sid;
      oid.push(sid);
      sid = 0;
    } else {
      sid += cur_octet & 0x7f;
      sid <<= 7;
      if (sid > Number.MAX_SAFE_INTEGER) throw 'Too big SID value: ' + sid;
    }
  }
  if (buf.slice(-1)[0] >= 0x80) throw 'Last octet in oid buffer has highest bit set to 1';
  return oid.join('.');
}
function asn1_parse_integer(buf) {
  if (buf.length > 6) {
    // may exceed MAX_SAFE_INTEGER, lets return hex
    return asn1_parse_any(buf);
  }
  var value = 0;
  var is_negative = false;
  if (buf[0] & 0x80) {
    is_negative = true;
    value = buf[0] & 0x7f;
    var compl_int = 1 << 8 * buf.length - 1;
  } else {
    value = buf[0];
  }
  if (buf.length > 1) {
    for (var n = 1; n < buf.length; n++) {
      value <<= 8;
      value += buf[n];
    }
  }
  if (is_negative) return value - compl_int;else return value;
}
function asn1_parse_ascii_string(buf) {
  return buf.toString();
}
function asn1_parse_ia5_string(buf) {
  if (is_ia5(buf)) return buf.toString();else throw 'Not a IA5String: ' + buf;
}
function asn1_parse_utf8_string(buf) {
  return buf.toString('utf8');
}
function asn1_parse_bmp_string(buf) {
  return asn1_parse_any(buf);
}
function asn1_parse_universal_string(buf) {
  return asn1_parse_any(buf);
}
function asn1_parse_bit_string(buf) {
  if (buf[0] == 0) return buf.slice(1).toString('hex');
  var shift = buf[0];
  if (shift > 7) throw 'Incorrect shift in bitstring: ' + shift;
  var value = '';
  var upper_bits = 0;
  var symbol = '';

  // shift string right and convert to hex
  for (var n = 1; n < buf.length; n++) {
    var char_code = buf[n] >> shift + upper_bits;
    symbol = char_code.toString(16);
    upper_bits = buf[n] << shift & 0xff;
    value += symbol;
  }
  return value;
}
function asn1_parse_octet_string(buf) {
  return asn1_parse_any(buf);
}
function asn1_parse_any(buf) {
  return buf.toString('hex');
}
function is_ia5(buf) {
  for (var n = 0; n < buf.length; n++) {
    var s = buf[n];
    if (s > 0x7e) return false;
  }
  return true;
}
function asn1_read_length(buf, pointer) {
  var s = buf[pointer];
  if (s == 0x80 || s == 0xff) throw 'indefinite length is not supported';
  if (s < 0x80) {
    // length is less than 128
    pointer++;
    return [s, pointer];
  } else {
    var l = s & 0x7f;
    if (l > 7) throw 'Too big length, exceeds MAX_SAFE_INTEGER: ' + l;
    if (pointer + l >= buf.length) throw 'Went out of buffer: ' + (pointer + l) + ' ' + buf.length;
    var length = 0;
    for (var n = 0; n < l; n++) {
      length += Math.pow(256, l - n - 1) * buf[++pointer];
      if (n == 6 && buf[pointer] > 0x1f) throw 'Too big length, exceeds MAX_SAFE_INTEGER';
    }
    return [length, pointer + 1];
  }
}
function asn1_parse_primitive(cls, tag, buf) {
  if (cls == 0) {
    switch (tag) {
      // INTEGER
      case 0x02:
        return asn1_parse_integer(buf);
      // BIT STRING
      case 0x03:
        try {
          return asn1_read(buf);
        } catch (e) {
          return asn1_parse_bit_string(buf);
        }
      // OCTET STRING
      case 0x04:
        try {
          return asn1_read(buf);
        } catch (e) {
          return asn1_parse_octet_string(buf);
        }
      // OBJECT IDENTIFIER
      case 0x06:
        return asn1_parse_oid(buf);
      // UTF8String
      case 0x0c:
        return asn1_parse_utf8_string(buf);
      // TIME
      case 0x0e:
      // NumericString
      case 0x12:
      // PrintableString
      case 0x13:
      // T61String
      case 0x14:
      // VideotexString
      case 0x15:
        return asn1_parse_ascii_string(buf);
      // IA5String
      case 0x16:
        return asn1_parse_ia5_string(buf);
      // UTCTime
      case 0x17:
      // GeneralizedTime
      case 0x18:
      // GraphicString
      case 0x19:
      // VisibleString
      case 0x1a:
      // GeneralString
      case 0x1b:
        return asn1_parse_ascii_string(buf);
      // UniversalString
      case 0x1c:
        return asn1_parse_universal_string(buf);
      // CHARACTER STRING
      case 0x1d:
        return asn1_parse_ascii_string(buf);
      // BMPString
      case 0x1e:
        return asn1_parse_bmp_string(buf);
      // DATE
      case 0x1f:
      // TIME-OF-DAY
      case 0x20:
      // DATE-TIME
      case 0x21:
      // DURATION
      case 0x22:
        return asn1_parse_ascii_string(buf);
      default:
        return asn1_parse_any(buf);
    }
  } else if (cls == 2) {
    switch (tag) {
      case 0x00:
        return asn1_parse_any(buf);
      case 0x01:
        return asn1_parse_ascii_string(buf);
      case 0x02:
        return asn1_parse_ascii_string(buf);
      case 0x06:
        return asn1_parse_ascii_string(buf);
      default:
        return asn1_parse_any(buf);
    }
  }
  return asn1_parse_any(buf);
}
function asn1_read(buf) {
  var a = [];
  var tag_class;
  var tag;
  var pointer = 0;
  var is_constructed;
  var s = '';
  var length;
  while (pointer < buf.length) {
    // read type: 7 & 8 bits define class, 6 bit if it is constructed
    s = buf[pointer];
    tag_class = s >> 6;
    is_constructed = s & 0x20;
    tag = s & 0x1f;
    if (tag == 0x1f) {
      tag = 0;
      var i = 0;
      do {
        if (i > 3) throw 'Too big tag value' + tag;
        i++;
        if (++pointer >= buf.length) throw 'Went out of buffer: ' + pointer + ' ' + buf.length;
        tag <<= 7;
        tag += buf[pointer] & 0x7f;
      } while (buf[pointer] > 0x80);
    }
    if (++pointer > buf.length) throw 'Went out of buffer: ' + pointer + ' ' + buf.length;
    var lp = asn1_read_length(buf, pointer);
    length = lp[0];
    pointer = lp[1];
    if (pointer + length > buf.length) throw 'length exceeds buf side: ' + length + ' ' + pointer + ' ' + buf.length;
    if (is_constructed) {
      a.push(asn1_read(buf.slice(pointer, pointer + length)));
    } else {
      a.push(asn1_parse_primitive(tag_class, tag, buf.slice(pointer, pointer + length)));
    }
    pointer += length;
  }
  return a;
}
function is_oid_exist(cert, oid) {
  for (var n = 0; n < cert.length; n++) {
    if (Array.isArray(cert[n])) {
      if (is_oid_exist(cert[n], oid)) return true;
    } else {
      if (cert[n] == oid) return true;
    }
  }
  return false;
}

// returns all the matching field with the specified 'oid' as a list
function get_oid_value_all(cert, oid) {
  var values = [];
  for (var n = 0; n < cert.length; n++) {
    if (Array.isArray(cert[n])) {
      var r = get_oid_value_all(cert[n], oid);
      if (r.length > 0) {
        values = values.concat(r);
      }
    } else {
      if (cert[n] == oid) {
        if (n < cert.length) {
          // push next element in array
          values.push(cert[n + 1]);
        }
      }
    }
  }
  return values;
}
function get_oid_value(cert, oid) {
  for (var n = 0; n < cert.length; n++) {
    if (Array.isArray(cert[n])) {
      var r = get_oid_value(cert[n], oid);
      if (r !== false) return r;
    } else {
      if (cert[n] == oid) {
        if (n < cert.length) {
          // return next element in array
          return cert[n + 1];
        }
      }
    }
  }
  return false;
}
function parse_pem_cert(pem) {
  var der = pem.split(/\n/);
  if (pem.match('CERTIFICATE')) {
    der = der.slice(1, -2);
  }

  // eslint-disable-next-line no-undef
  return asn1_read(Buffer.from(der.join(''), 'base64'));
}
var x509 = {
  asn1_read,
  parse_pem_cert,
  is_oid_exist,
  get_oid_value,
  get_oid_value_all
};

function _defineProperties(target, props) {
  for (var i = 0; i < props.length; i++) {
    var descriptor = props[i];
    descriptor.enumerable = descriptor.enumerable || false;
    descriptor.configurable = true;
    if ("value" in descriptor) descriptor.writable = true;
    Object.defineProperty(target, _toPropertyKey(descriptor.key), descriptor);
  }
}
function _createClass(Constructor, protoProps, staticProps) {
  if (protoProps) _defineProperties(Constructor.prototype, protoProps);
  if (staticProps) _defineProperties(Constructor, staticProps);
  Object.defineProperty(Constructor, "prototype", {
    writable: false
  });
  return Constructor;
}
function _inheritsLoose(subClass, superClass) {
  subClass.prototype = Object.create(superClass.prototype);
  subClass.prototype.constructor = subClass;
  _setPrototypeOf(subClass, superClass);
}
function _getPrototypeOf(o) {
  _getPrototypeOf = Object.setPrototypeOf ? Object.getPrototypeOf.bind() : function _getPrototypeOf(o) {
    return o.__proto__ || Object.getPrototypeOf(o);
  };
  return _getPrototypeOf(o);
}
function _setPrototypeOf(o, p) {
  _setPrototypeOf = Object.setPrototypeOf ? Object.setPrototypeOf.bind() : function _setPrototypeOf(o, p) {
    o.__proto__ = p;
    return o;
  };
  return _setPrototypeOf(o, p);
}
function _isNativeReflectConstruct() {
  if (typeof Reflect === "undefined" || !Reflect.construct) return false;
  if (Reflect.construct.sham) return false;
  if (typeof Proxy === "function") return true;
  try {
    Boolean.prototype.valueOf.call(Reflect.construct(Boolean, [], function () {}));
    return true;
  } catch (e) {
    return false;
  }
}
function _construct(Parent, args, Class) {
  if (_isNativeReflectConstruct()) {
    _construct = Reflect.construct.bind();
  } else {
    _construct = function _construct(Parent, args, Class) {
      var a = [null];
      a.push.apply(a, args);
      var Constructor = Function.bind.apply(Parent, a);
      var instance = new Constructor();
      if (Class) _setPrototypeOf(instance, Class.prototype);
      return instance;
    };
  }
  return _construct.apply(null, arguments);
}
function _isNativeFunction(fn) {
  return Function.toString.call(fn).indexOf("[native code]") !== -1;
}
function _wrapNativeSuper(Class) {
  var _cache = typeof Map === "function" ? new Map() : undefined;
  _wrapNativeSuper = function _wrapNativeSuper(Class) {
    if (Class === null || !_isNativeFunction(Class)) return Class;
    if (typeof Class !== "function") {
      throw new TypeError("Super expression must either be null or a function");
    }
    if (typeof _cache !== "undefined") {
      if (_cache.has(Class)) return _cache.get(Class);
      _cache.set(Class, Wrapper);
    }
    function Wrapper() {
      return _construct(Class, arguments, _getPrototypeOf(this).constructor);
    }
    Wrapper.prototype = Object.create(Class.prototype, {
      constructor: {
        value: Wrapper,
        enumerable: false,
        writable: true,
        configurable: true
      }
    });
    return _setPrototypeOf(Wrapper, Class);
  };
  return _wrapNativeSuper(Class);
}
function _objectDestructuringEmpty(obj) {
  if (obj == null) throw new TypeError("Cannot destructure " + obj);
}
function _objectWithoutPropertiesLoose(source, excluded) {
  if (source == null) return {};
  var target = {};
  var sourceKeys = Object.keys(source);
  var key, i;
  for (i = 0; i < sourceKeys.length; i++) {
    key = sourceKeys[i];
    if (excluded.indexOf(key) >= 0) continue;
    target[key] = source[key];
  }
  return target;
}
function _toPrimitive(input, hint) {
  if (typeof input !== "object" || input === null) return input;
  var prim = input[Symbol.toPrimitive];
  if (prim !== undefined) {
    var res = prim.call(input, hint || "default");
    if (typeof res !== "object") return res;
    throw new TypeError("@@toPrimitive must return a primitive value.");
  }
  return (hint === "string" ? String : Number)(input);
}
function _toPropertyKey(arg) {
  var key = _toPrimitive(arg, "string");
  return typeof key === "symbol" ? key : String(key);
}

/*!
 * MIT License
 * 
 * Copyright (c) 2017-2022 Peculiar Ventures, LLC
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 * 
 */

var ARRAY_BUFFER_NAME = "[object ArrayBuffer]";
var BufferSourceConverter = /*#__PURE__*/function () {
  function BufferSourceConverter() {}
  BufferSourceConverter.isArrayBuffer = function isArrayBuffer(data) {
    return Object.prototype.toString.call(data) === ARRAY_BUFFER_NAME;
  };
  BufferSourceConverter.toArrayBuffer = function toArrayBuffer(data) {
    if (this.isArrayBuffer(data)) {
      return data;
    }
    if (data.byteLength === data.buffer.byteLength) {
      return data.buffer;
    }
    return this.toUint8Array(data).slice().buffer;
  };
  BufferSourceConverter.toUint8Array = function toUint8Array(data) {
    return this.toView(data, Uint8Array);
  };
  BufferSourceConverter.toView = function toView(data, type) {
    if (data.constructor === type) {
      return data;
    }
    if (this.isArrayBuffer(data)) {
      return new type(data);
    }
    if (this.isArrayBufferView(data)) {
      return new type(data.buffer, data.byteOffset, data.byteLength);
    }
    throw new TypeError("The provided value is not of type '(ArrayBuffer or ArrayBufferView)'");
  };
  BufferSourceConverter.isBufferSource = function isBufferSource(data) {
    return this.isArrayBufferView(data) || this.isArrayBuffer(data);
  };
  BufferSourceConverter.isArrayBufferView = function isArrayBufferView(data) {
    return ArrayBuffer.isView(data) || data && this.isArrayBuffer(data.buffer);
  };
  BufferSourceConverter.isEqual = function isEqual(a, b) {
    var aView = BufferSourceConverter.toUint8Array(a);
    var bView = BufferSourceConverter.toUint8Array(b);
    if (aView.length !== bView.byteLength) {
      return false;
    }
    for (var i = 0; i < aView.length; i++) {
      if (aView[i] !== bView[i]) {
        return false;
      }
    }
    return true;
  };
  BufferSourceConverter.concat = function concat() {
    for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }
    if (Array.isArray(args[0])) {
      var buffers = args[0];
      var size = 0;
      for (var _i2 = 0; _i2 < buffers.length; _i2++) {
        var buffer = buffers[_i2];
        size += buffer.byteLength;
      }
      var res = new Uint8Array(size);
      var offset = 0;
      for (var _i4 = 0; _i4 < buffers.length; _i4++) {
        var _buffer = buffers[_i4];
        var view = this.toUint8Array(_buffer);
        res.set(view, offset);
        offset += view.length;
      }
      if (args[1]) {
        return this.toView(res, args[1]);
      }
      return res.buffer;
    } else {
      return this.concat(args);
    }
  };
  return BufferSourceConverter;
}();
var Utf8Converter = /*#__PURE__*/function () {
  function Utf8Converter() {}
  Utf8Converter.fromString = function fromString(text) {
    var s = unescape(encodeURIComponent(text));
    var uintArray = new Uint8Array(s.length);
    for (var i = 0; i < s.length; i++) {
      uintArray[i] = s.charCodeAt(i);
    }
    return uintArray.buffer;
  };
  Utf8Converter.toString = function toString(buffer) {
    var buf = BufferSourceConverter.toUint8Array(buffer);
    var encodedString = "";
    for (var i = 0; i < buf.length; i++) {
      encodedString += String.fromCharCode(buf[i]);
    }
    var decodedString = decodeURIComponent(escape(encodedString));
    return decodedString;
  };
  return Utf8Converter;
}();
var Utf16Converter = /*#__PURE__*/function () {
  function Utf16Converter() {}
  Utf16Converter.toString = function toString(buffer, littleEndian) {
    if (littleEndian === void 0) {
      littleEndian = false;
    }
    var arrayBuffer = BufferSourceConverter.toArrayBuffer(buffer);
    var dataView = new DataView(arrayBuffer);
    var res = "";
    for (var i = 0; i < arrayBuffer.byteLength; i += 2) {
      var code = dataView.getUint16(i, littleEndian);
      res += String.fromCharCode(code);
    }
    return res;
  };
  Utf16Converter.fromString = function fromString(text, littleEndian) {
    if (littleEndian === void 0) {
      littleEndian = false;
    }
    var res = new ArrayBuffer(text.length * 2);
    var dataView = new DataView(res);
    for (var i = 0; i < text.length; i++) {
      dataView.setUint16(i * 2, text.charCodeAt(i), littleEndian);
    }
    return res;
  };
  return Utf16Converter;
}();
var Convert = /*#__PURE__*/function () {
  function Convert() {}
  Convert.isHex = function isHex(data) {
    return typeof data === "string" && /^[a-z0-9]+$/i.test(data);
  };
  Convert.isBase64 = function isBase64(data) {
    return typeof data === "string" && /^(?:[A-Za-z0-9+/]{4})*(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?$/.test(data);
  };
  Convert.isBase64Url = function isBase64Url(data) {
    return typeof data === "string" && /^[a-zA-Z0-9-_]+$/i.test(data);
  };
  Convert.ToString = function ToString(buffer, enc) {
    if (enc === void 0) {
      enc = "utf8";
    }
    var buf = BufferSourceConverter.toUint8Array(buffer);
    switch (enc.toLowerCase()) {
      case "utf8":
        return this.ToUtf8String(buf);
      case "binary":
        return this.ToBinary(buf);
      case "hex":
        return this.ToHex(buf);
      case "base64":
        return this.ToBase64(buf);
      case "base64url":
        return this.ToBase64Url(buf);
      case "utf16le":
        return Utf16Converter.toString(buf, true);
      case "utf16":
      case "utf16be":
        return Utf16Converter.toString(buf);
      default:
        throw new Error(`Unknown type of encoding '${enc}'`);
    }
  };
  Convert.FromString = function FromString(str, enc) {
    if (enc === void 0) {
      enc = "utf8";
    }
    if (!str) {
      return new ArrayBuffer(0);
    }
    switch (enc.toLowerCase()) {
      case "utf8":
        return this.FromUtf8String(str);
      case "binary":
        return this.FromBinary(str);
      case "hex":
        return this.FromHex(str);
      case "base64":
        return this.FromBase64(str);
      case "base64url":
        return this.FromBase64Url(str);
      case "utf16le":
        return Utf16Converter.fromString(str, true);
      case "utf16":
      case "utf16be":
        return Utf16Converter.fromString(str);
      default:
        throw new Error(`Unknown type of encoding '${enc}'`);
    }
  };
  Convert.ToBase64 = function ToBase64(buffer) {
    var buf = BufferSourceConverter.toUint8Array(buffer);
    if (typeof btoa !== "undefined") {
      var binary = this.ToString(buf, "binary");
      return btoa(binary);
    } else {
      return Buffer.from(buf).toString("base64");
    }
  };
  Convert.FromBase64 = function FromBase64(base64) {
    var formatted = this.formatString(base64);
    if (!formatted) {
      return new ArrayBuffer(0);
    }
    if (!Convert.isBase64(formatted)) {
      throw new TypeError("Argument 'base64Text' is not Base64 encoded");
    }
    if (typeof atob !== "undefined") {
      return this.FromBinary(atob(formatted));
    } else {
      return new Uint8Array(Buffer.from(formatted, "base64")).buffer;
    }
  };
  Convert.FromBase64Url = function FromBase64Url(base64url) {
    var formatted = this.formatString(base64url);
    if (!formatted) {
      return new ArrayBuffer(0);
    }
    if (!Convert.isBase64Url(formatted)) {
      throw new TypeError("Argument 'base64url' is not Base64Url encoded");
    }
    return this.FromBase64(this.Base64Padding(formatted.replace(/\-/g, "+").replace(/\_/g, "/")));
  };
  Convert.ToBase64Url = function ToBase64Url(data) {
    return this.ToBase64(data).replace(/\+/g, "-").replace(/\//g, "_").replace(/\=/g, "");
  };
  Convert.FromUtf8String = function FromUtf8String(text, encoding) {
    if (encoding === void 0) {
      encoding = Convert.DEFAULT_UTF8_ENCODING;
    }
    switch (encoding) {
      case "ascii":
        return this.FromBinary(text);
      case "utf8":
        return Utf8Converter.fromString(text);
      case "utf16":
      case "utf16be":
        return Utf16Converter.fromString(text);
      case "utf16le":
      case "usc2":
        return Utf16Converter.fromString(text, true);
      default:
        throw new Error(`Unknown type of encoding '${encoding}'`);
    }
  };
  Convert.ToUtf8String = function ToUtf8String(buffer, encoding) {
    if (encoding === void 0) {
      encoding = Convert.DEFAULT_UTF8_ENCODING;
    }
    switch (encoding) {
      case "ascii":
        return this.ToBinary(buffer);
      case "utf8":
        return Utf8Converter.toString(buffer);
      case "utf16":
      case "utf16be":
        return Utf16Converter.toString(buffer);
      case "utf16le":
      case "usc2":
        return Utf16Converter.toString(buffer, true);
      default:
        throw new Error(`Unknown type of encoding '${encoding}'`);
    }
  };
  Convert.FromBinary = function FromBinary(text) {
    var stringLength = text.length;
    var resultView = new Uint8Array(stringLength);
    for (var i = 0; i < stringLength; i++) {
      resultView[i] = text.charCodeAt(i);
    }
    return resultView.buffer;
  };
  Convert.ToBinary = function ToBinary(buffer) {
    var buf = BufferSourceConverter.toUint8Array(buffer);
    var res = "";
    for (var i = 0; i < buf.length; i++) {
      res += String.fromCharCode(buf[i]);
    }
    return res;
  };
  Convert.ToHex = function ToHex(buffer) {
    var buf = BufferSourceConverter.toUint8Array(buffer);
    var splitter = "";
    var res = [];
    var len = buf.length;
    for (var i = 0; i < len; i++) {
      var char = buf[i].toString(16).padStart(2, "0");
      res.push(char);
    }
    return res.join(splitter);
  };
  Convert.FromHex = function FromHex(hexString) {
    var formatted = this.formatString(hexString);
    if (!formatted) {
      return new ArrayBuffer(0);
    }
    if (!Convert.isHex(formatted)) {
      throw new TypeError("Argument 'hexString' is not HEX encoded");
    }
    if (formatted.length % 2) {
      formatted = `0${formatted}`;
    }
    var res = new Uint8Array(formatted.length / 2);
    for (var i = 0; i < formatted.length; i = i + 2) {
      var c = formatted.slice(i, i + 2);
      res[i / 2] = parseInt(c, 16);
    }
    return res.buffer;
  };
  Convert.ToUtf16String = function ToUtf16String(buffer, littleEndian) {
    if (littleEndian === void 0) {
      littleEndian = false;
    }
    return Utf16Converter.toString(buffer, littleEndian);
  };
  Convert.FromUtf16String = function FromUtf16String(text, littleEndian) {
    if (littleEndian === void 0) {
      littleEndian = false;
    }
    return Utf16Converter.fromString(text, littleEndian);
  };
  Convert.Base64Padding = function Base64Padding(base64) {
    var padCount = 4 - base64.length % 4;
    if (padCount < 4) {
      for (var i = 0; i < padCount; i++) {
        base64 += "=";
      }
    }
    return base64;
  };
  Convert.formatString = function formatString(data) {
    return (data === null || data === void 0 ? void 0 : data.replace(/[\n\r\t ]/g, "")) || "";
  };
  return Convert;
}();
Convert.DEFAULT_UTF8_ENCODING = "utf8";

/*!
 Copyright (c) Peculiar Ventures, LLC
*/
function getParametersValue(parameters, name, defaultValue) {
  var _a;
  if (parameters instanceof Object === false) {
    return defaultValue;
  }
  return (_a = parameters[name]) !== null && _a !== void 0 ? _a : defaultValue;
}
function bufferToHexCodes(inputBuffer, inputOffset, inputLength, insertSpace) {
  if (inputOffset === void 0) {
    inputOffset = 0;
  }
  if (inputLength === void 0) {
    inputLength = inputBuffer.byteLength - inputOffset;
  }
  if (insertSpace === void 0) {
    insertSpace = false;
  }
  var result = "";
  for (var _i2 = 0, _Uint8Array2 = new Uint8Array(inputBuffer, inputOffset, inputLength); _i2 < _Uint8Array2.length; _i2++) {
    var item = _Uint8Array2[_i2];
    var str = item.toString(16).toUpperCase();
    if (str.length === 1) {
      result += "0";
    }
    result += str;
    if (insertSpace) {
      result += " ";
    }
  }
  return result.trim();
}
function utilFromBase(inputBuffer, inputBase) {
  var result = 0;
  if (inputBuffer.length === 1) {
    return inputBuffer[0];
  }
  for (var i = inputBuffer.length - 1; i >= 0; i--) {
    result += inputBuffer[inputBuffer.length - 1 - i] * Math.pow(2, inputBase * i);
  }
  return result;
}
function utilToBase(value, base, reserved) {
  if (reserved === void 0) {
    reserved = -1;
  }
  var internalReserved = reserved;
  var internalValue = value;
  var result = 0;
  var biggest = Math.pow(2, base);
  for (var i = 1; i < 8; i++) {
    if (value < biggest) {
      var retBuf = void 0;
      if (internalReserved < 0) {
        retBuf = new ArrayBuffer(i);
        result = i;
      } else {
        if (internalReserved < i) {
          return new ArrayBuffer(0);
        }
        retBuf = new ArrayBuffer(internalReserved);
        result = internalReserved;
      }
      var retView = new Uint8Array(retBuf);
      for (var j = i - 1; j >= 0; j--) {
        var basis = Math.pow(2, j * base);
        retView[result - j - 1] = Math.floor(internalValue / basis);
        internalValue -= retView[result - j - 1] * basis;
      }
      return retBuf;
    }
    biggest *= Math.pow(2, base);
  }
  return new ArrayBuffer(0);
}
function utilConcatBuf() {
  var outputLength = 0;
  var prevLength = 0;
  for (var _len = arguments.length, buffers = new Array(_len), _key = 0; _key < _len; _key++) {
    buffers[_key] = arguments[_key];
  }
  for (var _i4 = 0; _i4 < buffers.length; _i4++) {
    var buffer = buffers[_i4];
    outputLength += buffer.byteLength;
  }
  var retBuf = new ArrayBuffer(outputLength);
  var retView = new Uint8Array(retBuf);
  for (var _i6 = 0; _i6 < buffers.length; _i6++) {
    var _buffer = buffers[_i6];
    retView.set(new Uint8Array(_buffer), prevLength);
    prevLength += _buffer.byteLength;
  }
  return retBuf;
}
function utilConcatView() {
  var outputLength = 0;
  var prevLength = 0;
  for (var _len2 = arguments.length, views = new Array(_len2), _key2 = 0; _key2 < _len2; _key2++) {
    views[_key2] = arguments[_key2];
  }
  for (var _i8 = 0; _i8 < views.length; _i8++) {
    var view = views[_i8];
    outputLength += view.length;
  }
  var retBuf = new ArrayBuffer(outputLength);
  var retView = new Uint8Array(retBuf);
  for (var _i10 = 0; _i10 < views.length; _i10++) {
    var _view = views[_i10];
    retView.set(_view, prevLength);
    prevLength += _view.length;
  }
  return retView;
}
function utilDecodeTC() {
  var buf = new Uint8Array(this.valueHex);
  if (this.valueHex.byteLength >= 2) {
    var condition1 = buf[0] === 0xFF && buf[1] & 0x80;
    var condition2 = buf[0] === 0x00 && (buf[1] & 0x80) === 0x00;
    if (condition1 || condition2) {
      this.warnings.push("Needlessly long format");
    }
  }
  var bigIntBuffer = new ArrayBuffer(this.valueHex.byteLength);
  var bigIntView = new Uint8Array(bigIntBuffer);
  for (var i = 0; i < this.valueHex.byteLength; i++) {
    bigIntView[i] = 0;
  }
  bigIntView[0] = buf[0] & 0x80;
  var bigInt = utilFromBase(bigIntView, 8);
  var smallIntBuffer = new ArrayBuffer(this.valueHex.byteLength);
  var smallIntView = new Uint8Array(smallIntBuffer);
  for (var j = 0; j < this.valueHex.byteLength; j++) {
    smallIntView[j] = buf[j];
  }
  smallIntView[0] &= 0x7F;
  var smallInt = utilFromBase(smallIntView, 8);
  return smallInt - bigInt;
}
function utilEncodeTC(value) {
  var modValue = value < 0 ? value * -1 : value;
  var bigInt = 128;
  for (var i = 1; i < 8; i++) {
    if (modValue <= bigInt) {
      if (value < 0) {
        var smallInt = bigInt - modValue;
        var _retBuf = utilToBase(smallInt, 8, i);
        var _retView = new Uint8Array(_retBuf);
        _retView[0] |= 0x80;
        return _retBuf;
      }
      var retBuf = utilToBase(modValue, 8, i);
      var retView = new Uint8Array(retBuf);
      if (retView[0] & 0x80) {
        var tempBuf = retBuf.slice(0);
        var tempView = new Uint8Array(tempBuf);
        retBuf = new ArrayBuffer(retBuf.byteLength + 1);
        retView = new Uint8Array(retBuf);
        for (var k = 0; k < tempBuf.byteLength; k++) {
          retView[k + 1] = tempView[k];
        }
        retView[0] = 0x00;
      }
      return retBuf;
    }
    bigInt *= Math.pow(2, 8);
  }
  return new ArrayBuffer(0);
}
function isEqualBuffer(inputBuffer1, inputBuffer2) {
  if (inputBuffer1.byteLength !== inputBuffer2.byteLength) {
    return false;
  }
  var view1 = new Uint8Array(inputBuffer1);
  var view2 = new Uint8Array(inputBuffer2);
  for (var i = 0; i < view1.length; i++) {
    if (view1[i] !== view2[i]) {
      return false;
    }
  }
  return true;
}
function padNumber(inputNumber, fullLength) {
  var str = inputNumber.toString(10);
  if (fullLength < str.length) {
    return "";
  }
  var dif = fullLength - str.length;
  var padding = new Array(dif);
  for (var i = 0; i < dif; i++) {
    padding[i] = "0";
  }
  var paddingString = padding.join("");
  return paddingString.concat(str);
}
var base64Template = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=";
var base64UrlTemplate = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_=";
function toBase64(input, useUrlTemplate, skipPadding, skipLeadingZeros) {
  if (useUrlTemplate === void 0) {
    useUrlTemplate = false;
  }
  if (skipPadding === void 0) {
    skipPadding = false;
  }
  if (skipLeadingZeros === void 0) {
    skipLeadingZeros = false;
  }
  var i = 0;
  var flag1 = 0;
  var flag2 = 0;
  var output = "";
  var template = useUrlTemplate ? base64UrlTemplate : base64Template;
  if (skipLeadingZeros) {
    var nonZeroPosition = 0;
    for (var _i11 = 0; _i11 < input.length; _i11++) {
      if (input.charCodeAt(_i11) !== 0) {
        nonZeroPosition = _i11;
        break;
      }
    }
    input = input.slice(nonZeroPosition);
  }
  while (i < input.length) {
    var chr1 = input.charCodeAt(i++);
    if (i >= input.length) {
      flag1 = 1;
    }
    var chr2 = input.charCodeAt(i++);
    if (i >= input.length) {
      flag2 = 1;
    }
    var chr3 = input.charCodeAt(i++);
    var enc1 = chr1 >> 2;
    var enc2 = (chr1 & 0x03) << 4 | chr2 >> 4;
    var enc3 = (chr2 & 0x0F) << 2 | chr3 >> 6;
    var enc4 = chr3 & 0x3F;
    if (flag1 === 1) {
      enc3 = enc4 = 64;
    } else {
      if (flag2 === 1) {
        enc4 = 64;
      }
    }
    if (skipPadding) {
      if (enc3 === 64) {
        output += `${template.charAt(enc1)}${template.charAt(enc2)}`;
      } else {
        if (enc4 === 64) {
          output += `${template.charAt(enc1)}${template.charAt(enc2)}${template.charAt(enc3)}`;
        } else {
          output += `${template.charAt(enc1)}${template.charAt(enc2)}${template.charAt(enc3)}${template.charAt(enc4)}`;
        }
      }
    } else {
      output += `${template.charAt(enc1)}${template.charAt(enc2)}${template.charAt(enc3)}${template.charAt(enc4)}`;
    }
  }
  return output;
}
function fromBase64(input, useUrlTemplate, cutTailZeros) {
  if (useUrlTemplate === void 0) {
    useUrlTemplate = false;
  }
  if (cutTailZeros === void 0) {
    cutTailZeros = false;
  }
  var template = useUrlTemplate ? base64UrlTemplate : base64Template;
  function indexOf(toSearch) {
    for (var _i12 = 0; _i12 < 64; _i12++) {
      if (template.charAt(_i12) === toSearch) return _i12;
    }
    return 64;
  }
  function test(incoming) {
    return incoming === 64 ? 0x00 : incoming;
  }
  var i = 0;
  var output = "";
  while (i < input.length) {
    var enc1 = indexOf(input.charAt(i++));
    var enc2 = i >= input.length ? 0x00 : indexOf(input.charAt(i++));
    var enc3 = i >= input.length ? 0x00 : indexOf(input.charAt(i++));
    var enc4 = i >= input.length ? 0x00 : indexOf(input.charAt(i++));
    var chr1 = test(enc1) << 2 | test(enc2) >> 4;
    var chr2 = (test(enc2) & 0x0F) << 4 | test(enc3) >> 2;
    var chr3 = (test(enc3) & 0x03) << 6 | test(enc4);
    output += String.fromCharCode(chr1);
    if (enc3 !== 64) {
      output += String.fromCharCode(chr2);
    }
    if (enc4 !== 64) {
      output += String.fromCharCode(chr3);
    }
  }
  if (cutTailZeros) {
    var outputLength = output.length;
    var nonZeroStart = -1;
    for (var _i13 = outputLength - 1; _i13 >= 0; _i13--) {
      if (output.charCodeAt(_i13) !== 0) {
        nonZeroStart = _i13;
        break;
      }
    }
    if (nonZeroStart !== -1) {
      output = output.slice(0, nonZeroStart + 1);
    } else {
      output = "";
    }
  }
  return output;
}
function arrayBufferToString(buffer) {
  var resultString = "";
  var view = new Uint8Array(buffer);
  for (var _i15 = 0; _i15 < view.length; _i15++) {
    var element = view[_i15];
    resultString += String.fromCharCode(element);
  }
  return resultString;
}
function stringToArrayBuffer(str) {
  var stringLength = str.length;
  var resultBuffer = new ArrayBuffer(stringLength);
  var resultView = new Uint8Array(resultBuffer);
  for (var i = 0; i < stringLength; i++) {
    resultView[i] = str.charCodeAt(i);
  }
  return resultBuffer;
}
var log2 = Math.log(2);
function nearestPowerOf2(length) {
  var base = Math.log(length) / log2;
  var floor = Math.floor(base);
  var round = Math.round(base);
  return floor === round ? floor : round;
}
function clearProps(object, propsArray) {
  for (var _i17 = 0; _i17 < propsArray.length; _i17++) {
    var prop = propsArray[_i17];
    delete object[prop];
  }
}

var _excluded = ["name", "optional", "primitiveSchema"],
  _excluded2 = ["value"],
  _excluded3 = ["isHexOnly"],
  _excluded4 = ["value", "isIndefiniteForm"],
  _excluded5 = ["value"],
  _excluded6 = ["isConstructed"],
  _excluded7 = ["idBlock", "lenBlock"],
  _excluded8 = ["unusedBits", "isConstructed"],
  _excluded9 = ["idBlock", "lenBlock"],
  _excluded10 = ["value"],
  _excluded11 = ["valueDec", "isFirstSid"],
  _excluded12 = ["value"],
  _excluded13 = ["valueDec"],
  _excluded14 = ["value"],
  _excluded15 = ["value", "valueDate"],
  _excluded16 = ["value"],
  _excluded17 = ["value", "local"];
function assertBigInt() {
  if (typeof BigInt === "undefined") {
    throw new Error("BigInt is not defined. Your environment doesn't implement BigInt.");
  }
}
function concat(buffers) {
  var outputLength = 0;
  var prevLength = 0;
  for (var i = 0; i < buffers.length; i++) {
    var buffer = buffers[i];
    outputLength += buffer.byteLength;
  }
  var retView = new Uint8Array(outputLength);
  for (var _i = 0; _i < buffers.length; _i++) {
    var _buffer = buffers[_i];
    retView.set(new Uint8Array(_buffer), prevLength);
    prevLength += _buffer.byteLength;
  }
  return retView.buffer;
}
function checkBufferParams(baseBlock, inputBuffer, inputOffset, inputLength) {
  if (!(inputBuffer instanceof Uint8Array)) {
    baseBlock.error = "Wrong parameter: inputBuffer must be 'Uint8Array'";
    return false;
  }
  if (!inputBuffer.byteLength) {
    baseBlock.error = "Wrong parameter: inputBuffer has zero length";
    return false;
  }
  if (inputOffset < 0) {
    baseBlock.error = "Wrong parameter: inputOffset less than zero";
    return false;
  }
  if (inputLength < 0) {
    baseBlock.error = "Wrong parameter: inputLength less than zero";
    return false;
  }
  if (inputBuffer.byteLength - inputOffset - inputLength < 0) {
    baseBlock.error = "End of input reached before message was fully decoded (inconsistent offset and length values)";
    return false;
  }
  return true;
}
var ViewWriter = /*#__PURE__*/function () {
  function ViewWriter() {
    this.items = [];
  }
  var _proto = ViewWriter.prototype;
  _proto.write = function write(buf) {
    this.items.push(buf);
  };
  _proto.final = function final() {
    return concat(this.items);
  };
  return ViewWriter;
}();
var powers2 = [new Uint8Array([1])];
var digitsString = "0123456789";
var NAME = "name";
var VALUE_HEX_VIEW = "valueHexView";
var IS_HEX_ONLY = "isHexOnly";
var ID_BLOCK = "idBlock";
var TAG_CLASS = "tagClass";
var TAG_NUMBER = "tagNumber";
var IS_CONSTRUCTED = "isConstructed";
var FROM_BER = "fromBER";
var TO_BER = "toBER";
var LOCAL = "local";
var EMPTY_STRING$1 = "";
var EMPTY_BUFFER$1 = new ArrayBuffer(0);
var EMPTY_VIEW = new Uint8Array(0);
var END_OF_CONTENT_NAME = "EndOfContent";
var OCTET_STRING_NAME = "OCTET STRING";
var BIT_STRING_NAME = "BIT STRING";
function HexBlock(BaseClass) {
  var _a;
  return _a = /*#__PURE__*/function (_BaseClass) {
    _inheritsLoose(Some, _BaseClass);
    function Some() {
      var _this;
      var _a;
      for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
        args[_key] = arguments[_key];
      }
      _this = _BaseClass.call.apply(_BaseClass, [this].concat(args)) || this;
      var params = args[0] || {};
      _this.isHexOnly = (_a = params.isHexOnly) !== null && _a !== void 0 ? _a : false;
      _this.valueHexView = params.valueHex ? BufferSourceConverter.toUint8Array(params.valueHex) : EMPTY_VIEW;
      return _this;
    }
    var _proto2 = Some.prototype;
    _proto2.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
      var view = inputBuffer instanceof ArrayBuffer ? new Uint8Array(inputBuffer) : inputBuffer;
      if (!checkBufferParams(this, view, inputOffset, inputLength)) {
        return -1;
      }
      var endLength = inputOffset + inputLength;
      this.valueHexView = view.subarray(inputOffset, endLength);
      if (!this.valueHexView.length) {
        this.warnings.push("Zero buffer length");
        return inputOffset;
      }
      this.blockLength = inputLength;
      return endLength;
    };
    _proto2.toBER = function toBER(sizeOnly) {
      if (sizeOnly === void 0) {
        sizeOnly = false;
      }
      if (!this.isHexOnly) {
        this.error = "Flag 'isHexOnly' is not set, abort";
        return EMPTY_BUFFER$1;
      }
      if (sizeOnly) {
        return new ArrayBuffer(this.valueHexView.byteLength);
      }
      return this.valueHexView.byteLength === this.valueHexView.buffer.byteLength ? this.valueHexView.buffer : this.valueHexView.slice().buffer;
    };
    _proto2.toJSON = function toJSON() {
      return Object.assign({}, _BaseClass.prototype.toJSON.call(this), {
        isHexOnly: this.isHexOnly,
        valueHex: Convert.ToHex(this.valueHexView)
      });
    };
    _createClass(Some, [{
      key: "valueHex",
      get: function () {
        return this.valueHexView.slice().buffer;
      },
      set: function (value) {
        this.valueHexView = new Uint8Array(value);
      }
    }]);
    return Some;
  }(BaseClass), _a.NAME = "hexBlock", _a;
}
var LocalBaseBlock = /*#__PURE__*/function () {
  function LocalBaseBlock(_temp) {
    var _ref = _temp === void 0 ? {} : _temp,
      _ref$blockLength = _ref.blockLength,
      blockLength = _ref$blockLength === void 0 ? 0 : _ref$blockLength,
      _ref$error = _ref.error,
      error = _ref$error === void 0 ? EMPTY_STRING$1 : _ref$error,
      _ref$warnings = _ref.warnings,
      warnings = _ref$warnings === void 0 ? [] : _ref$warnings,
      _ref$valueBeforeDecod = _ref.valueBeforeDecode,
      valueBeforeDecode = _ref$valueBeforeDecod === void 0 ? EMPTY_VIEW : _ref$valueBeforeDecod;
    this.blockLength = blockLength;
    this.error = error;
    this.warnings = warnings;
    this.valueBeforeDecodeView = BufferSourceConverter.toUint8Array(valueBeforeDecode);
  }
  LocalBaseBlock.blockName = function blockName() {
    return this.NAME;
  };
  var _proto3 = LocalBaseBlock.prototype;
  _proto3.toJSON = function toJSON() {
    return {
      blockName: this.constructor.NAME,
      blockLength: this.blockLength,
      error: this.error,
      warnings: this.warnings,
      valueBeforeDecode: Convert.ToHex(this.valueBeforeDecodeView)
    };
  };
  _createClass(LocalBaseBlock, [{
    key: "valueBeforeDecode",
    get: function () {
      return this.valueBeforeDecodeView.slice().buffer;
    },
    set: function (value) {
      this.valueBeforeDecodeView = new Uint8Array(value);
    }
  }]);
  return LocalBaseBlock;
}();
LocalBaseBlock.NAME = "baseBlock";
var ValueBlock = /*#__PURE__*/function (_LocalBaseBlock) {
  _inheritsLoose(ValueBlock, _LocalBaseBlock);
  function ValueBlock() {
    return _LocalBaseBlock.apply(this, arguments) || this;
  }
  var _proto4 = ValueBlock.prototype;
  _proto4.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    throw TypeError("User need to make a specific function in a class which extends 'ValueBlock'");
  };
  _proto4.toBER = function toBER(sizeOnly, writer) {
    throw TypeError("User need to make a specific function in a class which extends 'ValueBlock'");
  };
  return ValueBlock;
}(LocalBaseBlock);
ValueBlock.NAME = "valueBlock";
var LocalIdentificationBlock = /*#__PURE__*/function (_HexBlock) {
  _inheritsLoose(LocalIdentificationBlock, _HexBlock);
  function LocalIdentificationBlock(_temp2) {
    var _this2;
    var _ref2 = _temp2 === void 0 ? {} : _temp2,
      _ref2$idBlock = _ref2.idBlock,
      idBlock = _ref2$idBlock === void 0 ? {} : _ref2$idBlock;
    var _a, _b, _c, _d;
    _this2 = _HexBlock.call(this) || this;
    if (idBlock) {
      _this2.isHexOnly = (_a = idBlock.isHexOnly) !== null && _a !== void 0 ? _a : false;
      _this2.valueHexView = idBlock.valueHex ? BufferSourceConverter.toUint8Array(idBlock.valueHex) : EMPTY_VIEW;
      _this2.tagClass = (_b = idBlock.tagClass) !== null && _b !== void 0 ? _b : -1;
      _this2.tagNumber = (_c = idBlock.tagNumber) !== null && _c !== void 0 ? _c : -1;
      _this2.isConstructed = (_d = idBlock.isConstructed) !== null && _d !== void 0 ? _d : false;
    } else {
      _this2.tagClass = -1;
      _this2.tagNumber = -1;
      _this2.isConstructed = false;
    }
    return _this2;
  }
  var _proto5 = LocalIdentificationBlock.prototype;
  _proto5.toBER = function toBER(sizeOnly) {
    if (sizeOnly === void 0) {
      sizeOnly = false;
    }
    var firstOctet = 0;
    switch (this.tagClass) {
      case 1:
        firstOctet |= 0x00;
        break;
      case 2:
        firstOctet |= 0x40;
        break;
      case 3:
        firstOctet |= 0x80;
        break;
      case 4:
        firstOctet |= 0xC0;
        break;
      default:
        this.error = "Unknown tag class";
        return EMPTY_BUFFER$1;
    }
    if (this.isConstructed) firstOctet |= 0x20;
    if (this.tagNumber < 31 && !this.isHexOnly) {
      var _retView = new Uint8Array(1);
      if (!sizeOnly) {
        var number = this.tagNumber;
        number &= 0x1F;
        firstOctet |= number;
        _retView[0] = firstOctet;
      }
      return _retView.buffer;
    }
    if (!this.isHexOnly) {
      var encodedBuf = utilToBase(this.tagNumber, 7);
      var encodedView = new Uint8Array(encodedBuf);
      var size = encodedBuf.byteLength;
      var _retView2 = new Uint8Array(size + 1);
      _retView2[0] = firstOctet | 0x1F;
      if (!sizeOnly) {
        for (var i = 0; i < size - 1; i++) _retView2[i + 1] = encodedView[i] | 0x80;
        _retView2[size] = encodedView[size - 1];
      }
      return _retView2.buffer;
    }
    var retView = new Uint8Array(this.valueHexView.byteLength + 1);
    retView[0] = firstOctet | 0x1F;
    if (!sizeOnly) {
      var curView = this.valueHexView;
      for (var _i2 = 0; _i2 < curView.length - 1; _i2++) retView[_i2 + 1] = curView[_i2] | 0x80;
      retView[this.valueHexView.byteLength] = curView[curView.length - 1];
    }
    return retView.buffer;
  };
  _proto5.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    var inputView = BufferSourceConverter.toUint8Array(inputBuffer);
    if (!checkBufferParams(this, inputView, inputOffset, inputLength)) {
      return -1;
    }
    var intBuffer = inputView.subarray(inputOffset, inputOffset + inputLength);
    if (intBuffer.length === 0) {
      this.error = "Zero buffer length";
      return -1;
    }
    var tagClassMask = intBuffer[0] & 0xC0;
    switch (tagClassMask) {
      case 0x00:
        this.tagClass = 1;
        break;
      case 0x40:
        this.tagClass = 2;
        break;
      case 0x80:
        this.tagClass = 3;
        break;
      case 0xC0:
        this.tagClass = 4;
        break;
      default:
        this.error = "Unknown tag class";
        return -1;
    }
    this.isConstructed = (intBuffer[0] & 0x20) === 0x20;
    this.isHexOnly = false;
    var tagNumberMask = intBuffer[0] & 0x1F;
    if (tagNumberMask !== 0x1F) {
      this.tagNumber = tagNumberMask;
      this.blockLength = 1;
    } else {
      var count = 1;
      var intTagNumberBuffer = this.valueHexView = new Uint8Array(255);
      var tagNumberBufferMaxLength = 255;
      while (intBuffer[count] & 0x80) {
        intTagNumberBuffer[count - 1] = intBuffer[count] & 0x7F;
        count++;
        if (count >= intBuffer.length) {
          this.error = "End of input reached before message was fully decoded";
          return -1;
        }
        if (count === tagNumberBufferMaxLength) {
          tagNumberBufferMaxLength += 255;
          var _tempBufferView = new Uint8Array(tagNumberBufferMaxLength);
          for (var i = 0; i < intTagNumberBuffer.length; i++) _tempBufferView[i] = intTagNumberBuffer[i];
          intTagNumberBuffer = this.valueHexView = new Uint8Array(tagNumberBufferMaxLength);
        }
      }
      this.blockLength = count + 1;
      intTagNumberBuffer[count - 1] = intBuffer[count] & 0x7F;
      var tempBufferView = new Uint8Array(count);
      for (var _i3 = 0; _i3 < count; _i3++) tempBufferView[_i3] = intTagNumberBuffer[_i3];
      intTagNumberBuffer = this.valueHexView = new Uint8Array(count);
      intTagNumberBuffer.set(tempBufferView);
      if (this.blockLength <= 9) this.tagNumber = utilFromBase(intTagNumberBuffer, 7);else {
        this.isHexOnly = true;
        this.warnings.push("Tag too long, represented as hex-coded");
      }
    }
    if (this.tagClass === 1 && this.isConstructed) {
      switch (this.tagNumber) {
        case 1:
        case 2:
        case 5:
        case 6:
        case 9:
        case 13:
        case 14:
        case 23:
        case 24:
        case 31:
        case 32:
        case 33:
        case 34:
          this.error = "Constructed encoding used for primitive type";
          return -1;
      }
    }
    return inputOffset + this.blockLength;
  };
  _proto5.toJSON = function toJSON() {
    return Object.assign({}, _HexBlock.prototype.toJSON.call(this), {
      tagClass: this.tagClass,
      tagNumber: this.tagNumber,
      isConstructed: this.isConstructed
    });
  };
  return LocalIdentificationBlock;
}(HexBlock(LocalBaseBlock));
LocalIdentificationBlock.NAME = "identificationBlock";
var LocalLengthBlock = /*#__PURE__*/function (_LocalBaseBlock2) {
  _inheritsLoose(LocalLengthBlock, _LocalBaseBlock2);
  function LocalLengthBlock(_temp3) {
    var _this3;
    var _ref3 = _temp3 === void 0 ? {} : _temp3,
      _ref3$lenBlock = _ref3.lenBlock,
      lenBlock = _ref3$lenBlock === void 0 ? {} : _ref3$lenBlock;
    var _a, _b, _c;
    _this3 = _LocalBaseBlock2.call(this) || this;
    _this3.isIndefiniteForm = (_a = lenBlock.isIndefiniteForm) !== null && _a !== void 0 ? _a : false;
    _this3.longFormUsed = (_b = lenBlock.longFormUsed) !== null && _b !== void 0 ? _b : false;
    _this3.length = (_c = lenBlock.length) !== null && _c !== void 0 ? _c : 0;
    return _this3;
  }
  var _proto6 = LocalLengthBlock.prototype;
  _proto6.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    var view = BufferSourceConverter.toUint8Array(inputBuffer);
    if (!checkBufferParams(this, view, inputOffset, inputLength)) {
      return -1;
    }
    var intBuffer = view.subarray(inputOffset, inputOffset + inputLength);
    if (intBuffer.length === 0) {
      this.error = "Zero buffer length";
      return -1;
    }
    if (intBuffer[0] === 0xFF) {
      this.error = "Length block 0xFF is reserved by standard";
      return -1;
    }
    this.isIndefiniteForm = intBuffer[0] === 0x80;
    if (this.isIndefiniteForm) {
      this.blockLength = 1;
      return inputOffset + this.blockLength;
    }
    this.longFormUsed = !!(intBuffer[0] & 0x80);
    if (this.longFormUsed === false) {
      this.length = intBuffer[0];
      this.blockLength = 1;
      return inputOffset + this.blockLength;
    }
    var count = intBuffer[0] & 0x7F;
    if (count > 8) {
      this.error = "Too big integer";
      return -1;
    }
    if (count + 1 > intBuffer.length) {
      this.error = "End of input reached before message was fully decoded";
      return -1;
    }
    var lenOffset = inputOffset + 1;
    var lengthBufferView = view.subarray(lenOffset, lenOffset + count);
    if (lengthBufferView[count - 1] === 0x00) this.warnings.push("Needlessly long encoded length");
    this.length = utilFromBase(lengthBufferView, 8);
    if (this.longFormUsed && this.length <= 127) this.warnings.push("Unnecessary usage of long length form");
    this.blockLength = count + 1;
    return inputOffset + this.blockLength;
  };
  _proto6.toBER = function toBER(sizeOnly) {
    if (sizeOnly === void 0) {
      sizeOnly = false;
    }
    var retBuf;
    var retView;
    if (this.length > 127) this.longFormUsed = true;
    if (this.isIndefiniteForm) {
      retBuf = new ArrayBuffer(1);
      if (sizeOnly === false) {
        retView = new Uint8Array(retBuf);
        retView[0] = 0x80;
      }
      return retBuf;
    }
    if (this.longFormUsed) {
      var encodedBuf = utilToBase(this.length, 8);
      if (encodedBuf.byteLength > 127) {
        this.error = "Too big length";
        return EMPTY_BUFFER$1;
      }
      retBuf = new ArrayBuffer(encodedBuf.byteLength + 1);
      if (sizeOnly) return retBuf;
      var encodedView = new Uint8Array(encodedBuf);
      retView = new Uint8Array(retBuf);
      retView[0] = encodedBuf.byteLength | 0x80;
      for (var i = 0; i < encodedBuf.byteLength; i++) retView[i + 1] = encodedView[i];
      return retBuf;
    }
    retBuf = new ArrayBuffer(1);
    if (sizeOnly === false) {
      retView = new Uint8Array(retBuf);
      retView[0] = this.length;
    }
    return retBuf;
  };
  _proto6.toJSON = function toJSON() {
    return Object.assign({}, _LocalBaseBlock2.prototype.toJSON.call(this), {
      isIndefiniteForm: this.isIndefiniteForm,
      longFormUsed: this.longFormUsed,
      length: this.length
    });
  };
  return LocalLengthBlock;
}(LocalBaseBlock);
LocalLengthBlock.NAME = "lengthBlock";
var typeStore = {};
var BaseBlock = /*#__PURE__*/function (_LocalBaseBlock3) {
  _inheritsLoose(BaseBlock, _LocalBaseBlock3);
  function BaseBlock(_ref4, valueBlockType) {
    var _this4;
    if (_ref4 === void 0) {
      _ref4 = {};
    }
    var _ref5 = _ref4,
      _ref5$name = _ref5.name,
      name = _ref5$name === void 0 ? EMPTY_STRING$1 : _ref5$name,
      _ref5$optional = _ref5.optional,
      optional = _ref5$optional === void 0 ? false : _ref5$optional,
      primitiveSchema = _ref5.primitiveSchema,
      parameters = _objectWithoutPropertiesLoose(_ref5, _excluded);
    _this4 = _LocalBaseBlock3.call(this, parameters) || this;
    _this4.name = name;
    _this4.optional = optional;
    if (primitiveSchema) {
      _this4.primitiveSchema = primitiveSchema;
    }
    _this4.idBlock = new LocalIdentificationBlock(parameters);
    _this4.lenBlock = new LocalLengthBlock(parameters);
    _this4.valueBlock = valueBlockType ? new valueBlockType(parameters) : new ValueBlock(parameters);
    return _this4;
  }
  var _proto7 = BaseBlock.prototype;
  _proto7.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    var resultOffset = this.valueBlock.fromBER(inputBuffer, inputOffset, this.lenBlock.isIndefiniteForm ? inputLength : this.lenBlock.length);
    if (resultOffset === -1) {
      this.error = this.valueBlock.error;
      return resultOffset;
    }
    if (!this.idBlock.error.length) this.blockLength += this.idBlock.blockLength;
    if (!this.lenBlock.error.length) this.blockLength += this.lenBlock.blockLength;
    if (!this.valueBlock.error.length) this.blockLength += this.valueBlock.blockLength;
    return resultOffset;
  };
  _proto7.toBER = function toBER(sizeOnly, writer) {
    var _writer = writer || new ViewWriter();
    if (!writer) {
      prepareIndefiniteForm(this);
    }
    var idBlockBuf = this.idBlock.toBER(sizeOnly);
    _writer.write(idBlockBuf);
    if (this.lenBlock.isIndefiniteForm) {
      _writer.write(new Uint8Array([0x80]).buffer);
      this.valueBlock.toBER(sizeOnly, _writer);
      _writer.write(new ArrayBuffer(2));
    } else {
      var valueBlockBuf = this.valueBlock.toBER(sizeOnly);
      this.lenBlock.length = valueBlockBuf.byteLength;
      var lenBlockBuf = this.lenBlock.toBER(sizeOnly);
      _writer.write(lenBlockBuf);
      _writer.write(valueBlockBuf);
    }
    if (!writer) {
      return _writer.final();
    }
    return EMPTY_BUFFER$1;
  };
  _proto7.toJSON = function toJSON() {
    var object = Object.assign({}, _LocalBaseBlock3.prototype.toJSON.call(this), {
      idBlock: this.idBlock.toJSON(),
      lenBlock: this.lenBlock.toJSON(),
      valueBlock: this.valueBlock.toJSON(),
      name: this.name,
      optional: this.optional
    });
    if (this.primitiveSchema) object.primitiveSchema = this.primitiveSchema.toJSON();
    return object;
  };
  _proto7.toString = function toString(encoding) {
    if (encoding === void 0) {
      encoding = "ascii";
    }
    if (encoding === "ascii") {
      return this.onAsciiEncoding();
    }
    return Convert.ToHex(this.toBER());
  };
  _proto7.onAsciiEncoding = function onAsciiEncoding() {
    return `${this.constructor.NAME} : ${Convert.ToHex(this.valueBlock.valueBeforeDecodeView)}`;
  };
  _proto7.isEqual = function isEqual(other) {
    if (this === other) {
      return true;
    }
    if (!(other instanceof this.constructor)) {
      return false;
    }
    var thisRaw = this.toBER();
    var otherRaw = other.toBER();
    return isEqualBuffer(thisRaw, otherRaw);
  };
  return BaseBlock;
}(LocalBaseBlock);
BaseBlock.NAME = "BaseBlock";
function prepareIndefiniteForm(baseBlock) {
  if (baseBlock instanceof typeStore.Constructed) {
    for (var _i5 = 0, _baseBlock$valueBlock2 = baseBlock.valueBlock.value; _i5 < _baseBlock$valueBlock2.length; _i5++) {
      var value = _baseBlock$valueBlock2[_i5];
      if (prepareIndefiniteForm(value)) {
        baseBlock.lenBlock.isIndefiniteForm = true;
      }
    }
  }
  return !!baseBlock.lenBlock.isIndefiniteForm;
}
var BaseStringBlock = /*#__PURE__*/function (_BaseBlock) {
  _inheritsLoose(BaseStringBlock, _BaseBlock);
  function BaseStringBlock(_ref6, stringValueBlockType) {
    var _this5;
    if (_ref6 === void 0) {
      _ref6 = {};
    }
    var _ref7 = _ref6,
      _ref7$value = _ref7.value,
      value = _ref7$value === void 0 ? EMPTY_STRING$1 : _ref7$value,
      parameters = _objectWithoutPropertiesLoose(_ref7, _excluded2);
    _this5 = _BaseBlock.call(this, parameters, stringValueBlockType) || this;
    if (value) {
      _this5.fromString(value);
    }
    return _this5;
  }
  var _proto8 = BaseStringBlock.prototype;
  _proto8.getValue = function getValue() {
    return this.valueBlock.value;
  };
  _proto8.setValue = function setValue(value) {
    this.valueBlock.value = value;
  };
  _proto8.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    var resultOffset = this.valueBlock.fromBER(inputBuffer, inputOffset, this.lenBlock.isIndefiniteForm ? inputLength : this.lenBlock.length);
    if (resultOffset === -1) {
      this.error = this.valueBlock.error;
      return resultOffset;
    }
    this.fromBuffer(this.valueBlock.valueHexView);
    if (!this.idBlock.error.length) this.blockLength += this.idBlock.blockLength;
    if (!this.lenBlock.error.length) this.blockLength += this.lenBlock.blockLength;
    if (!this.valueBlock.error.length) this.blockLength += this.valueBlock.blockLength;
    return resultOffset;
  };
  _proto8.onAsciiEncoding = function onAsciiEncoding() {
    return `${this.constructor.NAME} : '${this.valueBlock.value}'`;
  };
  return BaseStringBlock;
}(BaseBlock);
BaseStringBlock.NAME = "BaseStringBlock";
var LocalPrimitiveValueBlock = /*#__PURE__*/function (_HexBlock2) {
  _inheritsLoose(LocalPrimitiveValueBlock, _HexBlock2);
  function LocalPrimitiveValueBlock(_ref8) {
    var _this6;
    if (_ref8 === void 0) {
      _ref8 = {};
    }
    var _ref9 = _ref8,
      _ref9$isHexOnly = _ref9.isHexOnly,
      isHexOnly = _ref9$isHexOnly === void 0 ? true : _ref9$isHexOnly,
      parameters = _objectWithoutPropertiesLoose(_ref9, _excluded3);
    _this6 = _HexBlock2.call(this, parameters) || this;
    _this6.isHexOnly = isHexOnly;
    return _this6;
  }
  return LocalPrimitiveValueBlock;
}(HexBlock(ValueBlock));
LocalPrimitiveValueBlock.NAME = "PrimitiveValueBlock";
var _a$w;
var Primitive = /*#__PURE__*/function (_BaseBlock2) {
  _inheritsLoose(Primitive, _BaseBlock2);
  function Primitive(parameters) {
    var _this7;
    if (parameters === void 0) {
      parameters = {};
    }
    _this7 = _BaseBlock2.call(this, parameters, LocalPrimitiveValueBlock) || this;
    _this7.idBlock.isConstructed = false;
    return _this7;
  }
  return Primitive;
}(BaseBlock);
_a$w = Primitive;
(() => {
  typeStore.Primitive = _a$w;
})();
Primitive.NAME = "PRIMITIVE";
function localChangeType(inputObject, newType) {
  if (inputObject instanceof newType) {
    return inputObject;
  }
  var newObject = new newType();
  newObject.idBlock = inputObject.idBlock;
  newObject.lenBlock = inputObject.lenBlock;
  newObject.warnings = inputObject.warnings;
  newObject.valueBeforeDecodeView = inputObject.valueBeforeDecodeView;
  return newObject;
}
function localFromBER(inputBuffer, inputOffset, inputLength) {
  if (inputOffset === void 0) {
    inputOffset = 0;
  }
  if (inputLength === void 0) {
    inputLength = inputBuffer.length;
  }
  var incomingOffset = inputOffset;
  var returnObject = new BaseBlock({}, ValueBlock);
  var baseBlock = new LocalBaseBlock();
  if (!checkBufferParams(baseBlock, inputBuffer, inputOffset, inputLength)) {
    returnObject.error = baseBlock.error;
    return {
      offset: -1,
      result: returnObject
    };
  }
  var intBuffer = inputBuffer.subarray(inputOffset, inputOffset + inputLength);
  if (!intBuffer.length) {
    returnObject.error = "Zero buffer length";
    return {
      offset: -1,
      result: returnObject
    };
  }
  var resultOffset = returnObject.idBlock.fromBER(inputBuffer, inputOffset, inputLength);
  if (returnObject.idBlock.warnings.length) {
    returnObject.warnings.concat(returnObject.idBlock.warnings);
  }
  if (resultOffset === -1) {
    returnObject.error = returnObject.idBlock.error;
    return {
      offset: -1,
      result: returnObject
    };
  }
  inputOffset = resultOffset;
  inputLength -= returnObject.idBlock.blockLength;
  resultOffset = returnObject.lenBlock.fromBER(inputBuffer, inputOffset, inputLength);
  if (returnObject.lenBlock.warnings.length) {
    returnObject.warnings.concat(returnObject.lenBlock.warnings);
  }
  if (resultOffset === -1) {
    returnObject.error = returnObject.lenBlock.error;
    return {
      offset: -1,
      result: returnObject
    };
  }
  inputOffset = resultOffset;
  inputLength -= returnObject.lenBlock.blockLength;
  if (!returnObject.idBlock.isConstructed && returnObject.lenBlock.isIndefiniteForm) {
    returnObject.error = "Indefinite length form used for primitive encoding form";
    return {
      offset: -1,
      result: returnObject
    };
  }
  var newASN1Type = BaseBlock;
  switch (returnObject.idBlock.tagClass) {
    case 1:
      if (returnObject.idBlock.tagNumber >= 37 && returnObject.idBlock.isHexOnly === false) {
        returnObject.error = "UNIVERSAL 37 and upper tags are reserved by ASN.1 standard";
        return {
          offset: -1,
          result: returnObject
        };
      }
      switch (returnObject.idBlock.tagNumber) {
        case 0:
          if (returnObject.idBlock.isConstructed && returnObject.lenBlock.length > 0) {
            returnObject.error = "Type [UNIVERSAL 0] is reserved";
            return {
              offset: -1,
              result: returnObject
            };
          }
          newASN1Type = typeStore.EndOfContent;
          break;
        case 1:
          newASN1Type = typeStore.Boolean;
          break;
        case 2:
          newASN1Type = typeStore.Integer;
          break;
        case 3:
          newASN1Type = typeStore.BitString;
          break;
        case 4:
          newASN1Type = typeStore.OctetString;
          break;
        case 5:
          newASN1Type = typeStore.Null;
          break;
        case 6:
          newASN1Type = typeStore.ObjectIdentifier;
          break;
        case 10:
          newASN1Type = typeStore.Enumerated;
          break;
        case 12:
          newASN1Type = typeStore.Utf8String;
          break;
        case 13:
          newASN1Type = typeStore.RelativeObjectIdentifier;
          break;
        case 14:
          newASN1Type = typeStore.TIME;
          break;
        case 15:
          returnObject.error = "[UNIVERSAL 15] is reserved by ASN.1 standard";
          return {
            offset: -1,
            result: returnObject
          };
        case 16:
          newASN1Type = typeStore.Sequence;
          break;
        case 17:
          newASN1Type = typeStore.Set;
          break;
        case 18:
          newASN1Type = typeStore.NumericString;
          break;
        case 19:
          newASN1Type = typeStore.PrintableString;
          break;
        case 20:
          newASN1Type = typeStore.TeletexString;
          break;
        case 21:
          newASN1Type = typeStore.VideotexString;
          break;
        case 22:
          newASN1Type = typeStore.IA5String;
          break;
        case 23:
          newASN1Type = typeStore.UTCTime;
          break;
        case 24:
          newASN1Type = typeStore.GeneralizedTime;
          break;
        case 25:
          newASN1Type = typeStore.GraphicString;
          break;
        case 26:
          newASN1Type = typeStore.VisibleString;
          break;
        case 27:
          newASN1Type = typeStore.GeneralString;
          break;
        case 28:
          newASN1Type = typeStore.UniversalString;
          break;
        case 29:
          newASN1Type = typeStore.CharacterString;
          break;
        case 30:
          newASN1Type = typeStore.BmpString;
          break;
        case 31:
          newASN1Type = typeStore.DATE;
          break;
        case 32:
          newASN1Type = typeStore.TimeOfDay;
          break;
        case 33:
          newASN1Type = typeStore.DateTime;
          break;
        case 34:
          newASN1Type = typeStore.Duration;
          break;
        default:
          {
            var newObject = returnObject.idBlock.isConstructed ? new typeStore.Constructed() : new typeStore.Primitive();
            newObject.idBlock = returnObject.idBlock;
            newObject.lenBlock = returnObject.lenBlock;
            newObject.warnings = returnObject.warnings;
            returnObject = newObject;
          }
      }
      break;
    case 2:
    case 3:
    case 4:
    default:
      {
        newASN1Type = returnObject.idBlock.isConstructed ? typeStore.Constructed : typeStore.Primitive;
      }
  }
  returnObject = localChangeType(returnObject, newASN1Type);
  resultOffset = returnObject.fromBER(inputBuffer, inputOffset, returnObject.lenBlock.isIndefiniteForm ? inputLength : returnObject.lenBlock.length);
  returnObject.valueBeforeDecodeView = inputBuffer.subarray(incomingOffset, incomingOffset + returnObject.blockLength);
  return {
    offset: resultOffset,
    result: returnObject
  };
}
function fromBER(inputBuffer) {
  if (!inputBuffer.byteLength) {
    var result = new BaseBlock({}, ValueBlock);
    result.error = "Input buffer has zero length";
    return {
      offset: -1,
      result
    };
  }
  return localFromBER(BufferSourceConverter.toUint8Array(inputBuffer).slice(), 0, inputBuffer.byteLength);
}
function checkLen(indefiniteLength, length) {
  if (indefiniteLength) {
    return 1;
  }
  return length;
}
var LocalConstructedValueBlock = /*#__PURE__*/function (_ValueBlock) {
  _inheritsLoose(LocalConstructedValueBlock, _ValueBlock);
  function LocalConstructedValueBlock(_ref10) {
    var _this8;
    if (_ref10 === void 0) {
      _ref10 = {};
    }
    var _ref11 = _ref10,
      _ref11$value = _ref11.value,
      value = _ref11$value === void 0 ? [] : _ref11$value,
      _ref11$isIndefiniteFo = _ref11.isIndefiniteForm,
      isIndefiniteForm = _ref11$isIndefiniteFo === void 0 ? false : _ref11$isIndefiniteFo,
      parameters = _objectWithoutPropertiesLoose(_ref11, _excluded4);
    _this8 = _ValueBlock.call(this, parameters) || this;
    _this8.value = value;
    _this8.isIndefiniteForm = isIndefiniteForm;
    return _this8;
  }
  var _proto9 = LocalConstructedValueBlock.prototype;
  _proto9.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    var view = BufferSourceConverter.toUint8Array(inputBuffer);
    if (!checkBufferParams(this, view, inputOffset, inputLength)) {
      return -1;
    }
    this.valueBeforeDecodeView = view.subarray(inputOffset, inputOffset + inputLength);
    if (this.valueBeforeDecodeView.length === 0) {
      this.warnings.push("Zero buffer length");
      return inputOffset;
    }
    var currentOffset = inputOffset;
    while (checkLen(this.isIndefiniteForm, inputLength) > 0) {
      var returnObject = localFromBER(view, currentOffset, inputLength);
      if (returnObject.offset === -1) {
        this.error = returnObject.result.error;
        this.warnings.concat(returnObject.result.warnings);
        return -1;
      }
      currentOffset = returnObject.offset;
      this.blockLength += returnObject.result.blockLength;
      inputLength -= returnObject.result.blockLength;
      this.value.push(returnObject.result);
      if (this.isIndefiniteForm && returnObject.result.constructor.NAME === END_OF_CONTENT_NAME) {
        break;
      }
    }
    if (this.isIndefiniteForm) {
      if (this.value[this.value.length - 1].constructor.NAME === END_OF_CONTENT_NAME) {
        this.value.pop();
      } else {
        this.warnings.push("No EndOfContent block encoded");
      }
    }
    return currentOffset;
  };
  _proto9.toBER = function toBER(sizeOnly, writer) {
    var _writer = writer || new ViewWriter();
    for (var i = 0; i < this.value.length; i++) {
      this.value[i].toBER(sizeOnly, _writer);
    }
    if (!writer) {
      return _writer.final();
    }
    return EMPTY_BUFFER$1;
  };
  _proto9.toJSON = function toJSON() {
    var object = Object.assign({}, _ValueBlock.prototype.toJSON.call(this), {
      isIndefiniteForm: this.isIndefiniteForm,
      value: []
    });
    for (var _i7 = 0, _this$value2 = this.value; _i7 < _this$value2.length; _i7++) {
      var value = _this$value2[_i7];
      object.value.push(value.toJSON());
    }
    return object;
  };
  return LocalConstructedValueBlock;
}(ValueBlock);
LocalConstructedValueBlock.NAME = "ConstructedValueBlock";
var _a$v;
var Constructed = /*#__PURE__*/function (_BaseBlock3) {
  _inheritsLoose(Constructed, _BaseBlock3);
  function Constructed(parameters) {
    var _this9;
    if (parameters === void 0) {
      parameters = {};
    }
    _this9 = _BaseBlock3.call(this, parameters, LocalConstructedValueBlock) || this;
    _this9.idBlock.isConstructed = true;
    return _this9;
  }
  var _proto10 = Constructed.prototype;
  _proto10.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    this.valueBlock.isIndefiniteForm = this.lenBlock.isIndefiniteForm;
    var resultOffset = this.valueBlock.fromBER(inputBuffer, inputOffset, this.lenBlock.isIndefiniteForm ? inputLength : this.lenBlock.length);
    if (resultOffset === -1) {
      this.error = this.valueBlock.error;
      return resultOffset;
    }
    if (!this.idBlock.error.length) this.blockLength += this.idBlock.blockLength;
    if (!this.lenBlock.error.length) this.blockLength += this.lenBlock.blockLength;
    if (!this.valueBlock.error.length) this.blockLength += this.valueBlock.blockLength;
    return resultOffset;
  };
  _proto10.onAsciiEncoding = function onAsciiEncoding() {
    var values = [];
    for (var _i9 = 0, _this$valueBlock$valu2 = this.valueBlock.value; _i9 < _this$valueBlock$valu2.length; _i9++) {
      var value = _this$valueBlock$valu2[_i9];
      values.push(value.toString("ascii").split("\n").map(o => `  ${o}`).join("\n"));
    }
    var blockName = this.idBlock.tagClass === 3 ? `[${this.idBlock.tagNumber}]` : this.constructor.NAME;
    return values.length ? `${blockName} :\n${values.join("\n")}` : `${blockName} :`;
  };
  return Constructed;
}(BaseBlock);
_a$v = Constructed;
(() => {
  typeStore.Constructed = _a$v;
})();
Constructed.NAME = "CONSTRUCTED";
var LocalEndOfContentValueBlock = /*#__PURE__*/function (_ValueBlock2) {
  _inheritsLoose(LocalEndOfContentValueBlock, _ValueBlock2);
  function LocalEndOfContentValueBlock() {
    return _ValueBlock2.apply(this, arguments) || this;
  }
  var _proto11 = LocalEndOfContentValueBlock.prototype;
  _proto11.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    return inputOffset;
  };
  _proto11.toBER = function toBER(sizeOnly) {
    return EMPTY_BUFFER$1;
  };
  return LocalEndOfContentValueBlock;
}(ValueBlock);
LocalEndOfContentValueBlock.override = "EndOfContentValueBlock";
var _a$u;
var EndOfContent = /*#__PURE__*/function (_BaseBlock4) {
  _inheritsLoose(EndOfContent, _BaseBlock4);
  function EndOfContent(parameters) {
    var _this10;
    if (parameters === void 0) {
      parameters = {};
    }
    _this10 = _BaseBlock4.call(this, parameters, LocalEndOfContentValueBlock) || this;
    _this10.idBlock.tagClass = 1;
    _this10.idBlock.tagNumber = 0;
    return _this10;
  }
  return EndOfContent;
}(BaseBlock);
_a$u = EndOfContent;
(() => {
  typeStore.EndOfContent = _a$u;
})();
EndOfContent.NAME = END_OF_CONTENT_NAME;
var _a$t;
var Null = /*#__PURE__*/function (_BaseBlock5) {
  _inheritsLoose(Null, _BaseBlock5);
  function Null(parameters) {
    var _this11;
    if (parameters === void 0) {
      parameters = {};
    }
    _this11 = _BaseBlock5.call(this, parameters, ValueBlock) || this;
    _this11.idBlock.tagClass = 1;
    _this11.idBlock.tagNumber = 5;
    return _this11;
  }
  var _proto12 = Null.prototype;
  _proto12.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    if (this.lenBlock.length > 0) this.warnings.push("Non-zero length of value block for Null type");
    if (!this.idBlock.error.length) this.blockLength += this.idBlock.blockLength;
    if (!this.lenBlock.error.length) this.blockLength += this.lenBlock.blockLength;
    this.blockLength += inputLength;
    if (inputOffset + inputLength > inputBuffer.byteLength) {
      this.error = "End of input reached before message was fully decoded (inconsistent offset and length values)";
      return -1;
    }
    return inputOffset + inputLength;
  };
  _proto12.toBER = function toBER(sizeOnly, writer) {
    var retBuf = new ArrayBuffer(2);
    if (!sizeOnly) {
      var retView = new Uint8Array(retBuf);
      retView[0] = 0x05;
      retView[1] = 0x00;
    }
    if (writer) {
      writer.write(retBuf);
    }
    return retBuf;
  };
  _proto12.onAsciiEncoding = function onAsciiEncoding() {
    return `${this.constructor.NAME}`;
  };
  return Null;
}(BaseBlock);
_a$t = Null;
(() => {
  typeStore.Null = _a$t;
})();
Null.NAME = "NULL";
var LocalBooleanValueBlock = /*#__PURE__*/function (_HexBlock3) {
  _inheritsLoose(LocalBooleanValueBlock, _HexBlock3);
  function LocalBooleanValueBlock(_ref12) {
    var _this12;
    if (_ref12 === void 0) {
      _ref12 = {};
    }
    var _ref13 = _ref12,
      value = _ref13.value,
      parameters = _objectWithoutPropertiesLoose(_ref13, _excluded5);
    _this12 = _HexBlock3.call(this, parameters) || this;
    if (parameters.valueHex) {
      _this12.valueHexView = BufferSourceConverter.toUint8Array(parameters.valueHex);
    } else {
      _this12.valueHexView = new Uint8Array(1);
    }
    if (value) {
      _this12.value = value;
    }
    return _this12;
  }
  var _proto13 = LocalBooleanValueBlock.prototype;
  _proto13.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    var inputView = BufferSourceConverter.toUint8Array(inputBuffer);
    if (!checkBufferParams(this, inputView, inputOffset, inputLength)) {
      return -1;
    }
    this.valueHexView = inputView.subarray(inputOffset, inputOffset + inputLength);
    if (inputLength > 1) this.warnings.push("Boolean value encoded in more then 1 octet");
    this.isHexOnly = true;
    utilDecodeTC.call(this);
    this.blockLength = inputLength;
    return inputOffset + inputLength;
  };
  _proto13.toBER = function toBER() {
    return this.valueHexView.slice();
  };
  _proto13.toJSON = function toJSON() {
    return Object.assign({}, _HexBlock3.prototype.toJSON.call(this), {
      value: this.value
    });
  };
  _createClass(LocalBooleanValueBlock, [{
    key: "value",
    get: function () {
      for (var _i11 = 0, _this$valueHexView2 = this.valueHexView; _i11 < _this$valueHexView2.length; _i11++) {
        var octet = _this$valueHexView2[_i11];
        if (octet > 0) {
          return true;
        }
      }
      return false;
    },
    set: function (value) {
      this.valueHexView[0] = value ? 0xFF : 0x00;
    }
  }]);
  return LocalBooleanValueBlock;
}(HexBlock(ValueBlock));
LocalBooleanValueBlock.NAME = "BooleanValueBlock";
var _a$s;
var Boolean$1 = /*#__PURE__*/function (_BaseBlock6) {
  _inheritsLoose(Boolean, _BaseBlock6);
  function Boolean(parameters) {
    var _this13;
    if (parameters === void 0) {
      parameters = {};
    }
    _this13 = _BaseBlock6.call(this, parameters, LocalBooleanValueBlock) || this;
    _this13.idBlock.tagClass = 1;
    _this13.idBlock.tagNumber = 1;
    return _this13;
  }
  var _proto14 = Boolean.prototype;
  _proto14.getValue = function getValue() {
    return this.valueBlock.value;
  };
  _proto14.setValue = function setValue(value) {
    this.valueBlock.value = value;
  };
  _proto14.onAsciiEncoding = function onAsciiEncoding() {
    return `${this.constructor.NAME} : ${this.getValue}`;
  };
  return Boolean;
}(BaseBlock);
_a$s = Boolean$1;
(() => {
  typeStore.Boolean = _a$s;
})();
Boolean$1.NAME = "BOOLEAN";
var LocalOctetStringValueBlock = /*#__PURE__*/function (_HexBlock4) {
  _inheritsLoose(LocalOctetStringValueBlock, _HexBlock4);
  function LocalOctetStringValueBlock(_ref14) {
    var _this14;
    if (_ref14 === void 0) {
      _ref14 = {};
    }
    var _ref15 = _ref14,
      _ref15$isConstructed = _ref15.isConstructed,
      isConstructed = _ref15$isConstructed === void 0 ? false : _ref15$isConstructed,
      parameters = _objectWithoutPropertiesLoose(_ref15, _excluded6);
    _this14 = _HexBlock4.call(this, parameters) || this;
    _this14.isConstructed = isConstructed;
    return _this14;
  }
  var _proto15 = LocalOctetStringValueBlock.prototype;
  _proto15.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    var resultOffset = 0;
    if (this.isConstructed) {
      this.isHexOnly = false;
      resultOffset = LocalConstructedValueBlock.prototype.fromBER.call(this, inputBuffer, inputOffset, inputLength);
      if (resultOffset === -1) return resultOffset;
      for (var i = 0; i < this.value.length; i++) {
        var currentBlockName = this.value[i].constructor.NAME;
        if (currentBlockName === END_OF_CONTENT_NAME) {
          if (this.isIndefiniteForm) break;else {
            this.error = "EndOfContent is unexpected, OCTET STRING may consists of OCTET STRINGs only";
            return -1;
          }
        }
        if (currentBlockName !== OCTET_STRING_NAME) {
          this.error = "OCTET STRING may consists of OCTET STRINGs only";
          return -1;
        }
      }
    } else {
      this.isHexOnly = true;
      resultOffset = _HexBlock4.prototype.fromBER.call(this, inputBuffer, inputOffset, inputLength);
      this.blockLength = inputLength;
    }
    return resultOffset;
  };
  _proto15.toBER = function toBER(sizeOnly, writer) {
    if (this.isConstructed) return LocalConstructedValueBlock.prototype.toBER.call(this, sizeOnly, writer);
    return sizeOnly ? new ArrayBuffer(this.valueHexView.byteLength) : this.valueHexView.slice().buffer;
  };
  _proto15.toJSON = function toJSON() {
    return Object.assign({}, _HexBlock4.prototype.toJSON.call(this), {
      isConstructed: this.isConstructed
    });
  };
  return LocalOctetStringValueBlock;
}(HexBlock(LocalConstructedValueBlock));
LocalOctetStringValueBlock.NAME = "OctetStringValueBlock";
var _a$r;
var OctetString = /*#__PURE__*/function (_BaseBlock7) {
  _inheritsLoose(OctetString, _BaseBlock7);
  function OctetString(_ref16) {
    var _this15;
    if (_ref16 === void 0) {
      _ref16 = {};
    }
    var _ref17 = _ref16,
      _ref17$idBlock = _ref17.idBlock,
      idBlock = _ref17$idBlock === void 0 ? {} : _ref17$idBlock,
      _ref17$lenBlock = _ref17.lenBlock,
      lenBlock = _ref17$lenBlock === void 0 ? {} : _ref17$lenBlock,
      parameters = _objectWithoutPropertiesLoose(_ref17, _excluded7);
    var _b, _c;
    (_b = parameters.isConstructed) !== null && _b !== void 0 ? _b : parameters.isConstructed = !!((_c = parameters.value) === null || _c === void 0 ? void 0 : _c.length);
    _this15 = _BaseBlock7.call(this, Object.assign({
      idBlock: Object.assign({
        isConstructed: parameters.isConstructed
      }, idBlock),
      lenBlock: Object.assign({}, lenBlock, {
        isIndefiniteForm: !!parameters.isIndefiniteForm
      })
    }, parameters), LocalOctetStringValueBlock) || this;
    _this15.idBlock.tagClass = 1;
    _this15.idBlock.tagNumber = 4;
    return _this15;
  }
  var _proto16 = OctetString.prototype;
  _proto16.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    this.valueBlock.isConstructed = this.idBlock.isConstructed;
    this.valueBlock.isIndefiniteForm = this.lenBlock.isIndefiniteForm;
    if (inputLength === 0) {
      if (this.idBlock.error.length === 0) this.blockLength += this.idBlock.blockLength;
      if (this.lenBlock.error.length === 0) this.blockLength += this.lenBlock.blockLength;
      return inputOffset;
    }
    if (!this.valueBlock.isConstructed) {
      var view = inputBuffer instanceof ArrayBuffer ? new Uint8Array(inputBuffer) : inputBuffer;
      var buf = view.subarray(inputOffset, inputOffset + inputLength);
      try {
        if (buf.byteLength) {
          var asn = localFromBER(buf, 0, buf.byteLength);
          if (asn.offset !== -1 && asn.offset === inputLength) {
            this.valueBlock.value = [asn.result];
          }
        }
      } catch (e) {}
    }
    return _BaseBlock7.prototype.fromBER.call(this, inputBuffer, inputOffset, inputLength);
  };
  _proto16.onAsciiEncoding = function onAsciiEncoding() {
    if (this.valueBlock.isConstructed || this.valueBlock.value && this.valueBlock.value.length) {
      return Constructed.prototype.onAsciiEncoding.call(this);
    }
    return `${this.constructor.NAME} : ${Convert.ToHex(this.valueBlock.valueHexView)}`;
  };
  _proto16.getValue = function getValue() {
    if (!this.idBlock.isConstructed) {
      return this.valueBlock.valueHexView.slice().buffer;
    }
    var array = [];
    for (var _i13 = 0, _this$valueBlock$valu4 = this.valueBlock.value; _i13 < _this$valueBlock$valu4.length; _i13++) {
      var content = _this$valueBlock$valu4[_i13];
      if (content instanceof OctetString) {
        array.push(content.valueBlock.valueHexView);
      }
    }
    return BufferSourceConverter.concat(array);
  };
  return OctetString;
}(BaseBlock);
_a$r = OctetString;
(() => {
  typeStore.OctetString = _a$r;
})();
OctetString.NAME = OCTET_STRING_NAME;
var LocalBitStringValueBlock = /*#__PURE__*/function (_HexBlock5) {
  _inheritsLoose(LocalBitStringValueBlock, _HexBlock5);
  function LocalBitStringValueBlock(_ref18) {
    var _this16;
    if (_ref18 === void 0) {
      _ref18 = {};
    }
    var _ref19 = _ref18,
      _ref19$unusedBits = _ref19.unusedBits,
      unusedBits = _ref19$unusedBits === void 0 ? 0 : _ref19$unusedBits,
      _ref19$isConstructed = _ref19.isConstructed,
      isConstructed = _ref19$isConstructed === void 0 ? false : _ref19$isConstructed,
      parameters = _objectWithoutPropertiesLoose(_ref19, _excluded8);
    _this16 = _HexBlock5.call(this, parameters) || this;
    _this16.unusedBits = unusedBits;
    _this16.isConstructed = isConstructed;
    _this16.blockLength = _this16.valueHexView.byteLength;
    return _this16;
  }
  var _proto17 = LocalBitStringValueBlock.prototype;
  _proto17.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    if (!inputLength) {
      return inputOffset;
    }
    var resultOffset = -1;
    if (this.isConstructed) {
      resultOffset = LocalConstructedValueBlock.prototype.fromBER.call(this, inputBuffer, inputOffset, inputLength);
      if (resultOffset === -1) return resultOffset;
      for (var _i15 = 0, _this$value4 = this.value; _i15 < _this$value4.length; _i15++) {
        var value = _this$value4[_i15];
        var currentBlockName = value.constructor.NAME;
        if (currentBlockName === END_OF_CONTENT_NAME) {
          if (this.isIndefiniteForm) break;else {
            this.error = "EndOfContent is unexpected, BIT STRING may consists of BIT STRINGs only";
            return -1;
          }
        }
        if (currentBlockName !== BIT_STRING_NAME) {
          this.error = "BIT STRING may consists of BIT STRINGs only";
          return -1;
        }
        var valueBlock = value.valueBlock;
        if (this.unusedBits > 0 && valueBlock.unusedBits > 0) {
          this.error = "Using of \"unused bits\" inside constructive BIT STRING allowed for least one only";
          return -1;
        }
        this.unusedBits = valueBlock.unusedBits;
      }
      return resultOffset;
    }
    var inputView = BufferSourceConverter.toUint8Array(inputBuffer);
    if (!checkBufferParams(this, inputView, inputOffset, inputLength)) {
      return -1;
    }
    var intBuffer = inputView.subarray(inputOffset, inputOffset + inputLength);
    this.unusedBits = intBuffer[0];
    if (this.unusedBits > 7) {
      this.error = "Unused bits for BitString must be in range 0-7";
      return -1;
    }
    if (!this.unusedBits) {
      var buf = intBuffer.subarray(1);
      try {
        if (buf.byteLength) {
          var asn = localFromBER(buf, 0, buf.byteLength);
          if (asn.offset !== -1 && asn.offset === inputLength - 1) {
            this.value = [asn.result];
          }
        }
      } catch (e) {}
    }
    this.valueHexView = intBuffer.subarray(1);
    this.blockLength = intBuffer.length;
    return inputOffset + inputLength;
  };
  _proto17.toBER = function toBER(sizeOnly, writer) {
    if (this.isConstructed) {
      return LocalConstructedValueBlock.prototype.toBER.call(this, sizeOnly, writer);
    }
    if (sizeOnly) {
      return new ArrayBuffer(this.valueHexView.byteLength + 1);
    }
    if (!this.valueHexView.byteLength) {
      return EMPTY_BUFFER$1;
    }
    var retView = new Uint8Array(this.valueHexView.length + 1);
    retView[0] = this.unusedBits;
    retView.set(this.valueHexView, 1);
    return retView.buffer;
  };
  _proto17.toJSON = function toJSON() {
    return Object.assign({}, _HexBlock5.prototype.toJSON.call(this), {
      unusedBits: this.unusedBits,
      isConstructed: this.isConstructed
    });
  };
  return LocalBitStringValueBlock;
}(HexBlock(LocalConstructedValueBlock));
LocalBitStringValueBlock.NAME = "BitStringValueBlock";
var _a$q;
var BitString = /*#__PURE__*/function (_BaseBlock8) {
  _inheritsLoose(BitString, _BaseBlock8);
  function BitString(_ref20) {
    var _this17;
    if (_ref20 === void 0) {
      _ref20 = {};
    }
    var _ref21 = _ref20,
      _ref21$idBlock = _ref21.idBlock,
      idBlock = _ref21$idBlock === void 0 ? {} : _ref21$idBlock,
      _ref21$lenBlock = _ref21.lenBlock,
      lenBlock = _ref21$lenBlock === void 0 ? {} : _ref21$lenBlock,
      parameters = _objectWithoutPropertiesLoose(_ref21, _excluded9);
    var _b, _c;
    (_b = parameters.isConstructed) !== null && _b !== void 0 ? _b : parameters.isConstructed = !!((_c = parameters.value) === null || _c === void 0 ? void 0 : _c.length);
    _this17 = _BaseBlock8.call(this, Object.assign({
      idBlock: Object.assign({
        isConstructed: parameters.isConstructed
      }, idBlock),
      lenBlock: Object.assign({}, lenBlock, {
        isIndefiniteForm: !!parameters.isIndefiniteForm
      })
    }, parameters), LocalBitStringValueBlock) || this;
    _this17.idBlock.tagClass = 1;
    _this17.idBlock.tagNumber = 3;
    return _this17;
  }
  var _proto18 = BitString.prototype;
  _proto18.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    this.valueBlock.isConstructed = this.idBlock.isConstructed;
    this.valueBlock.isIndefiniteForm = this.lenBlock.isIndefiniteForm;
    return _BaseBlock8.prototype.fromBER.call(this, inputBuffer, inputOffset, inputLength);
  };
  _proto18.onAsciiEncoding = function onAsciiEncoding() {
    if (this.valueBlock.isConstructed || this.valueBlock.value && this.valueBlock.value.length) {
      return Constructed.prototype.onAsciiEncoding.call(this);
    } else {
      var bits = [];
      var valueHex = this.valueBlock.valueHexView;
      for (var _i17 = 0; _i17 < valueHex.length; _i17++) {
        var byte = valueHex[_i17];
        bits.push(byte.toString(2).padStart(8, "0"));
      }
      var bitsStr = bits.join("");
      return `${this.constructor.NAME} : ${bitsStr.substring(0, bitsStr.length - this.valueBlock.unusedBits)}`;
    }
  };
  return BitString;
}(BaseBlock);
_a$q = BitString;
(() => {
  typeStore.BitString = _a$q;
})();
BitString.NAME = BIT_STRING_NAME;
var _a$p;
function viewAdd(first, second) {
  var c = new Uint8Array([0]);
  var firstView = new Uint8Array(first);
  var secondView = new Uint8Array(second);
  var firstViewCopy = firstView.slice(0);
  var firstViewCopyLength = firstViewCopy.length - 1;
  var secondViewCopy = secondView.slice(0);
  var secondViewCopyLength = secondViewCopy.length - 1;
  var value = 0;
  var max = secondViewCopyLength < firstViewCopyLength ? firstViewCopyLength : secondViewCopyLength;
  var counter = 0;
  for (var i = max; i >= 0; i--, counter++) {
    switch (true) {
      case counter < secondViewCopy.length:
        value = firstViewCopy[firstViewCopyLength - counter] + secondViewCopy[secondViewCopyLength - counter] + c[0];
        break;
      default:
        value = firstViewCopy[firstViewCopyLength - counter] + c[0];
    }
    c[0] = value / 10;
    switch (true) {
      case counter >= firstViewCopy.length:
        firstViewCopy = utilConcatView(new Uint8Array([value % 10]), firstViewCopy);
        break;
      default:
        firstViewCopy[firstViewCopyLength - counter] = value % 10;
    }
  }
  if (c[0] > 0) firstViewCopy = utilConcatView(c, firstViewCopy);
  return firstViewCopy;
}
function power2(n) {
  if (n >= powers2.length) {
    for (var p = powers2.length; p <= n; p++) {
      var c = new Uint8Array([0]);
      var digits = powers2[p - 1].slice(0);
      for (var i = digits.length - 1; i >= 0; i--) {
        var newValue = new Uint8Array([(digits[i] << 1) + c[0]]);
        c[0] = newValue[0] / 10;
        digits[i] = newValue[0] % 10;
      }
      if (c[0] > 0) digits = utilConcatView(c, digits);
      powers2.push(digits);
    }
  }
  return powers2[n];
}
function viewSub(first, second) {
  var b = 0;
  var firstView = new Uint8Array(first);
  var secondView = new Uint8Array(second);
  var firstViewCopy = firstView.slice(0);
  var firstViewCopyLength = firstViewCopy.length - 1;
  var secondViewCopy = secondView.slice(0);
  var secondViewCopyLength = secondViewCopy.length - 1;
  var value;
  var counter = 0;
  for (var i = secondViewCopyLength; i >= 0; i--, counter++) {
    value = firstViewCopy[firstViewCopyLength - counter] - secondViewCopy[secondViewCopyLength - counter] - b;
    switch (true) {
      case value < 0:
        b = 1;
        firstViewCopy[firstViewCopyLength - counter] = value + 10;
        break;
      default:
        b = 0;
        firstViewCopy[firstViewCopyLength - counter] = value;
    }
  }
  if (b > 0) {
    for (var _i18 = firstViewCopyLength - secondViewCopyLength + 1; _i18 >= 0; _i18--, counter++) {
      value = firstViewCopy[firstViewCopyLength - counter] - b;
      if (value < 0) {
        b = 1;
        firstViewCopy[firstViewCopyLength - counter] = value + 10;
      } else {
        b = 0;
        firstViewCopy[firstViewCopyLength - counter] = value;
        break;
      }
    }
  }
  return firstViewCopy.slice();
}
var LocalIntegerValueBlock = /*#__PURE__*/function (_HexBlock6) {
  _inheritsLoose(LocalIntegerValueBlock, _HexBlock6);
  function LocalIntegerValueBlock(_ref22) {
    var _this18;
    if (_ref22 === void 0) {
      _ref22 = {};
    }
    var _ref23 = _ref22,
      value = _ref23.value,
      parameters = _objectWithoutPropertiesLoose(_ref23, _excluded10);
    _this18 = _HexBlock6.call(this, parameters) || this;
    _this18._valueDec = 0;
    if (parameters.valueHex) {
      _this18.setValueHex();
    }
    if (value !== undefined) {
      _this18.valueDec = value;
    }
    return _this18;
  }
  var _proto19 = LocalIntegerValueBlock.prototype;
  _proto19.setValueHex = function setValueHex() {
    if (this.valueHexView.length >= 4) {
      this.warnings.push("Too big Integer for decoding, hex only");
      this.isHexOnly = true;
      this._valueDec = 0;
    } else {
      this.isHexOnly = false;
      if (this.valueHexView.length > 0) {
        this._valueDec = utilDecodeTC.call(this);
      }
    }
  };
  _proto19.fromDER = function fromDER(inputBuffer, inputOffset, inputLength, expectedLength) {
    if (expectedLength === void 0) {
      expectedLength = 0;
    }
    var offset = this.fromBER(inputBuffer, inputOffset, inputLength);
    if (offset === -1) return offset;
    var view = this.valueHexView;
    if (view[0] === 0x00 && (view[1] & 0x80) !== 0) {
      this.valueHexView = view.subarray(1);
    } else {
      if (expectedLength !== 0) {
        if (view.length < expectedLength) {
          if (expectedLength - view.length > 1) expectedLength = view.length + 1;
          this.valueHexView = view.subarray(expectedLength - view.length);
        }
      }
    }
    return offset;
  };
  _proto19.toDER = function toDER(sizeOnly) {
    if (sizeOnly === void 0) {
      sizeOnly = false;
    }
    var view = this.valueHexView;
    switch (true) {
      case (view[0] & 0x80) !== 0:
        {
          var updatedView = new Uint8Array(this.valueHexView.length + 1);
          updatedView[0] = 0x00;
          updatedView.set(view, 1);
          this.valueHexView = updatedView;
        }
        break;
      case view[0] === 0x00 && (view[1] & 0x80) === 0:
        {
          this.valueHexView = this.valueHexView.subarray(1);
        }
        break;
    }
    return this.toBER(sizeOnly);
  };
  _proto19.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    var resultOffset = _HexBlock6.prototype.fromBER.call(this, inputBuffer, inputOffset, inputLength);
    if (resultOffset === -1) {
      return resultOffset;
    }
    this.setValueHex();
    return resultOffset;
  };
  _proto19.toBER = function toBER(sizeOnly) {
    return sizeOnly ? new ArrayBuffer(this.valueHexView.length) : this.valueHexView.slice().buffer;
  };
  _proto19.toJSON = function toJSON() {
    return Object.assign({}, _HexBlock6.prototype.toJSON.call(this), {
      valueDec: this.valueDec
    });
  };
  _proto19.toString = function toString() {
    var firstBit = this.valueHexView.length * 8 - 1;
    var digits = new Uint8Array(this.valueHexView.length * 8 / 3);
    var bitNumber = 0;
    var currentByte;
    var asn1View = this.valueHexView;
    var result = "";
    var flag = false;
    for (var byteNumber = asn1View.byteLength - 1; byteNumber >= 0; byteNumber--) {
      currentByte = asn1View[byteNumber];
      for (var i = 0; i < 8; i++) {
        if ((currentByte & 1) === 1) {
          switch (bitNumber) {
            case firstBit:
              digits = viewSub(power2(bitNumber), digits);
              result = "-";
              break;
            default:
              digits = viewAdd(digits, power2(bitNumber));
          }
        }
        bitNumber++;
        currentByte >>= 1;
      }
    }
    for (var _i19 = 0; _i19 < digits.length; _i19++) {
      if (digits[_i19]) flag = true;
      if (flag) result += digitsString.charAt(digits[_i19]);
    }
    if (flag === false) result += digitsString.charAt(0);
    return result;
  };
  _createClass(LocalIntegerValueBlock, [{
    key: "valueDec",
    get: function () {
      return this._valueDec;
    },
    set: function (v) {
      this._valueDec = v;
      this.isHexOnly = false;
      this.valueHexView = new Uint8Array(utilEncodeTC(v));
    }
  }]);
  return LocalIntegerValueBlock;
}(HexBlock(ValueBlock));
_a$p = LocalIntegerValueBlock;
LocalIntegerValueBlock.NAME = "IntegerValueBlock";
(() => {
  Object.defineProperty(_a$p.prototype, "valueHex", {
    set: function (v) {
      this.valueHexView = new Uint8Array(v);
      this.setValueHex();
    },
    get: function () {
      return this.valueHexView.slice().buffer;
    }
  });
})();
var _a$o;
var Integer = /*#__PURE__*/function (_BaseBlock9) {
  _inheritsLoose(Integer, _BaseBlock9);
  function Integer(parameters) {
    var _this19;
    if (parameters === void 0) {
      parameters = {};
    }
    _this19 = _BaseBlock9.call(this, parameters, LocalIntegerValueBlock) || this;
    _this19.idBlock.tagClass = 1;
    _this19.idBlock.tagNumber = 2;
    return _this19;
  }
  var _proto20 = Integer.prototype;
  _proto20.toBigInt = function toBigInt() {
    assertBigInt();
    return BigInt(this.valueBlock.toString());
  };
  Integer.fromBigInt = function fromBigInt(value) {
    assertBigInt();
    var bigIntValue = BigInt(value);
    var writer = new ViewWriter();
    var hex = bigIntValue.toString(16).replace(/^-/, "");
    var view = new Uint8Array(Convert.FromHex(hex));
    if (bigIntValue < 0) {
      var first = new Uint8Array(view.length + (view[0] & 0x80 ? 1 : 0));
      first[0] |= 0x80;
      var firstInt = BigInt(`0x${Convert.ToHex(first)}`);
      var secondInt = firstInt + bigIntValue;
      var second = BufferSourceConverter.toUint8Array(Convert.FromHex(secondInt.toString(16)));
      second[0] |= 0x80;
      writer.write(second);
    } else {
      if (view[0] & 0x80) {
        writer.write(new Uint8Array([0]));
      }
      writer.write(view);
    }
    var res = new Integer({
      valueHex: writer.final()
    });
    return res;
  };
  _proto20.convertToDER = function convertToDER() {
    var integer = new Integer({
      valueHex: this.valueBlock.valueHexView
    });
    integer.valueBlock.toDER();
    return integer;
  };
  _proto20.convertFromDER = function convertFromDER() {
    return new Integer({
      valueHex: this.valueBlock.valueHexView[0] === 0 ? this.valueBlock.valueHexView.subarray(1) : this.valueBlock.valueHexView
    });
  };
  _proto20.onAsciiEncoding = function onAsciiEncoding() {
    return `${this.constructor.NAME} : ${this.valueBlock.toString()}`;
  };
  return Integer;
}(BaseBlock);
_a$o = Integer;
(() => {
  typeStore.Integer = _a$o;
})();
Integer.NAME = "INTEGER";
var _a$n;
var Enumerated = /*#__PURE__*/function (_Integer) {
  _inheritsLoose(Enumerated, _Integer);
  function Enumerated(parameters) {
    var _this20;
    if (parameters === void 0) {
      parameters = {};
    }
    _this20 = _Integer.call(this, parameters) || this;
    _this20.idBlock.tagClass = 1;
    _this20.idBlock.tagNumber = 10;
    return _this20;
  }
  return Enumerated;
}(Integer);
_a$n = Enumerated;
(() => {
  typeStore.Enumerated = _a$n;
})();
Enumerated.NAME = "ENUMERATED";
var LocalSidValueBlock = /*#__PURE__*/function (_HexBlock7) {
  _inheritsLoose(LocalSidValueBlock, _HexBlock7);
  function LocalSidValueBlock(_ref24) {
    var _this21;
    if (_ref24 === void 0) {
      _ref24 = {};
    }
    var _ref25 = _ref24,
      _ref25$valueDec = _ref25.valueDec,
      valueDec = _ref25$valueDec === void 0 ? -1 : _ref25$valueDec,
      _ref25$isFirstSid = _ref25.isFirstSid,
      isFirstSid = _ref25$isFirstSid === void 0 ? false : _ref25$isFirstSid,
      parameters = _objectWithoutPropertiesLoose(_ref25, _excluded11);
    _this21 = _HexBlock7.call(this, parameters) || this;
    _this21.valueDec = valueDec;
    _this21.isFirstSid = isFirstSid;
    return _this21;
  }
  var _proto21 = LocalSidValueBlock.prototype;
  _proto21.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    if (!inputLength) {
      return inputOffset;
    }
    var inputView = BufferSourceConverter.toUint8Array(inputBuffer);
    if (!checkBufferParams(this, inputView, inputOffset, inputLength)) {
      return -1;
    }
    var intBuffer = inputView.subarray(inputOffset, inputOffset + inputLength);
    this.valueHexView = new Uint8Array(inputLength);
    for (var i = 0; i < inputLength; i++) {
      this.valueHexView[i] = intBuffer[i] & 0x7F;
      this.blockLength++;
      if ((intBuffer[i] & 0x80) === 0x00) break;
    }
    var tempView = new Uint8Array(this.blockLength);
    for (var _i20 = 0; _i20 < this.blockLength; _i20++) {
      tempView[_i20] = this.valueHexView[_i20];
    }
    this.valueHexView = tempView;
    if ((intBuffer[this.blockLength - 1] & 0x80) !== 0x00) {
      this.error = "End of input reached before message was fully decoded";
      return -1;
    }
    if (this.valueHexView[0] === 0x00) this.warnings.push("Needlessly long format of SID encoding");
    if (this.blockLength <= 8) this.valueDec = utilFromBase(this.valueHexView, 7);else {
      this.isHexOnly = true;
      this.warnings.push("Too big SID for decoding, hex only");
    }
    return inputOffset + this.blockLength;
  };
  _proto21.toBER = function toBER(sizeOnly) {
    if (this.isHexOnly) {
      if (sizeOnly) return new ArrayBuffer(this.valueHexView.byteLength);
      var curView = this.valueHexView;
      var _retView3 = new Uint8Array(this.blockLength);
      for (var i = 0; i < this.blockLength - 1; i++) _retView3[i] = curView[i] | 0x80;
      _retView3[this.blockLength - 1] = curView[this.blockLength - 1];
      return _retView3.buffer;
    }
    var encodedBuf = utilToBase(this.valueDec, 7);
    if (encodedBuf.byteLength === 0) {
      this.error = "Error during encoding SID value";
      return EMPTY_BUFFER$1;
    }
    var retView = new Uint8Array(encodedBuf.byteLength);
    if (!sizeOnly) {
      var encodedView = new Uint8Array(encodedBuf);
      var len = encodedBuf.byteLength - 1;
      for (var _i21 = 0; _i21 < len; _i21++) retView[_i21] = encodedView[_i21] | 0x80;
      retView[len] = encodedView[len];
    }
    return retView;
  };
  _proto21.toString = function toString() {
    var result = "";
    if (this.isHexOnly) result = Convert.ToHex(this.valueHexView);else {
      if (this.isFirstSid) {
        var sidValue = this.valueDec;
        if (this.valueDec <= 39) result = "0.";else {
          if (this.valueDec <= 79) {
            result = "1.";
            sidValue -= 40;
          } else {
            result = "2.";
            sidValue -= 80;
          }
        }
        result += sidValue.toString();
      } else result = this.valueDec.toString();
    }
    return result;
  };
  _proto21.toJSON = function toJSON() {
    return Object.assign({}, _HexBlock7.prototype.toJSON.call(this), {
      valueDec: this.valueDec,
      isFirstSid: this.isFirstSid
    });
  };
  _createClass(LocalSidValueBlock, [{
    key: "valueBigInt",
    set: function (value) {
      assertBigInt();
      var bits = BigInt(value).toString(2);
      while (bits.length % 7) {
        bits = "0" + bits;
      }
      var bytes = new Uint8Array(bits.length / 7);
      for (var i = 0; i < bytes.length; i++) {
        bytes[i] = parseInt(bits.slice(i * 7, i * 7 + 7), 2) + (i + 1 < bytes.length ? 0x80 : 0);
      }
      this.fromBER(bytes.buffer, 0, bytes.length);
    }
  }]);
  return LocalSidValueBlock;
}(HexBlock(ValueBlock));
LocalSidValueBlock.NAME = "sidBlock";
var LocalObjectIdentifierValueBlock = /*#__PURE__*/function (_ValueBlock3) {
  _inheritsLoose(LocalObjectIdentifierValueBlock, _ValueBlock3);
  function LocalObjectIdentifierValueBlock(_ref26) {
    var _this22;
    if (_ref26 === void 0) {
      _ref26 = {};
    }
    var _ref27 = _ref26,
      _ref27$value = _ref27.value,
      value = _ref27$value === void 0 ? EMPTY_STRING$1 : _ref27$value,
      parameters = _objectWithoutPropertiesLoose(_ref27, _excluded12);
    _this22 = _ValueBlock3.call(this, parameters) || this;
    _this22.value = [];
    if (value) {
      _this22.fromString(value);
    }
    return _this22;
  }
  var _proto22 = LocalObjectIdentifierValueBlock.prototype;
  _proto22.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    var resultOffset = inputOffset;
    while (inputLength > 0) {
      var sidBlock = new LocalSidValueBlock();
      resultOffset = sidBlock.fromBER(inputBuffer, resultOffset, inputLength);
      if (resultOffset === -1) {
        this.blockLength = 0;
        this.error = sidBlock.error;
        return resultOffset;
      }
      if (this.value.length === 0) sidBlock.isFirstSid = true;
      this.blockLength += sidBlock.blockLength;
      inputLength -= sidBlock.blockLength;
      this.value.push(sidBlock);
    }
    return resultOffset;
  };
  _proto22.toBER = function toBER(sizeOnly) {
    var retBuffers = [];
    for (var i = 0; i < this.value.length; i++) {
      var valueBuf = this.value[i].toBER(sizeOnly);
      if (valueBuf.byteLength === 0) {
        this.error = this.value[i].error;
        return EMPTY_BUFFER$1;
      }
      retBuffers.push(valueBuf);
    }
    return concat(retBuffers);
  };
  _proto22.fromString = function fromString(string) {
    this.value = [];
    var pos1 = 0;
    var pos2 = 0;
    var sid = "";
    var flag = false;
    do {
      pos2 = string.indexOf(".", pos1);
      if (pos2 === -1) sid = string.substring(pos1);else sid = string.substring(pos1, pos2);
      pos1 = pos2 + 1;
      if (flag) {
        var sidBlock = this.value[0];
        var plus = 0;
        switch (sidBlock.valueDec) {
          case 0:
            break;
          case 1:
            plus = 40;
            break;
          case 2:
            plus = 80;
            break;
          default:
            this.value = [];
            return;
        }
        var parsedSID = parseInt(sid, 10);
        if (isNaN(parsedSID)) return;
        sidBlock.valueDec = parsedSID + plus;
        flag = false;
      } else {
        var _sidBlock = new LocalSidValueBlock();
        if (sid > Number.MAX_SAFE_INTEGER) {
          assertBigInt();
          var sidValue = BigInt(sid);
          _sidBlock.valueBigInt = sidValue;
        } else {
          _sidBlock.valueDec = parseInt(sid, 10);
          if (isNaN(_sidBlock.valueDec)) return;
        }
        if (!this.value.length) {
          _sidBlock.isFirstSid = true;
          flag = true;
        }
        this.value.push(_sidBlock);
      }
    } while (pos2 !== -1);
  };
  _proto22.toString = function toString() {
    var result = "";
    var isHexOnly = false;
    for (var i = 0; i < this.value.length; i++) {
      isHexOnly = this.value[i].isHexOnly;
      var sidStr = this.value[i].toString();
      if (i !== 0) result = `${result}.`;
      if (isHexOnly) {
        sidStr = `{${sidStr}}`;
        if (this.value[i].isFirstSid) result = `2.{${sidStr} - 80}`;else result += sidStr;
      } else result += sidStr;
    }
    return result;
  };
  _proto22.toJSON = function toJSON() {
    var object = Object.assign({}, _ValueBlock3.prototype.toJSON.call(this), {
      value: this.toString(),
      sidArray: []
    });
    for (var i = 0; i < this.value.length; i++) {
      object.sidArray.push(this.value[i].toJSON());
    }
    return object;
  };
  return LocalObjectIdentifierValueBlock;
}(ValueBlock);
LocalObjectIdentifierValueBlock.NAME = "ObjectIdentifierValueBlock";
var _a$m;
var ObjectIdentifier = /*#__PURE__*/function (_BaseBlock10) {
  _inheritsLoose(ObjectIdentifier, _BaseBlock10);
  function ObjectIdentifier(parameters) {
    var _this23;
    if (parameters === void 0) {
      parameters = {};
    }
    _this23 = _BaseBlock10.call(this, parameters, LocalObjectIdentifierValueBlock) || this;
    _this23.idBlock.tagClass = 1;
    _this23.idBlock.tagNumber = 6;
    return _this23;
  }
  var _proto23 = ObjectIdentifier.prototype;
  _proto23.getValue = function getValue() {
    return this.valueBlock.toString();
  };
  _proto23.setValue = function setValue(value) {
    this.valueBlock.fromString(value);
  };
  _proto23.onAsciiEncoding = function onAsciiEncoding() {
    return `${this.constructor.NAME} : ${this.valueBlock.toString() || "empty"}`;
  };
  _proto23.toJSON = function toJSON() {
    return Object.assign({}, _BaseBlock10.prototype.toJSON.call(this), {
      value: this.getValue()
    });
  };
  return ObjectIdentifier;
}(BaseBlock);
_a$m = ObjectIdentifier;
(() => {
  typeStore.ObjectIdentifier = _a$m;
})();
ObjectIdentifier.NAME = "OBJECT IDENTIFIER";
var LocalRelativeSidValueBlock = /*#__PURE__*/function (_HexBlock8) {
  _inheritsLoose(LocalRelativeSidValueBlock, _HexBlock8);
  function LocalRelativeSidValueBlock(_ref28) {
    var _this24;
    if (_ref28 === void 0) {
      _ref28 = {};
    }
    var _ref29 = _ref28,
      _ref29$valueDec = _ref29.valueDec,
      valueDec = _ref29$valueDec === void 0 ? 0 : _ref29$valueDec,
      parameters = _objectWithoutPropertiesLoose(_ref29, _excluded13);
    _this24 = _HexBlock8.call(this, parameters) || this;
    _this24.valueDec = valueDec;
    return _this24;
  }
  var _proto24 = LocalRelativeSidValueBlock.prototype;
  _proto24.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    if (inputLength === 0) return inputOffset;
    var inputView = BufferSourceConverter.toUint8Array(inputBuffer);
    if (!checkBufferParams(this, inputView, inputOffset, inputLength)) return -1;
    var intBuffer = inputView.subarray(inputOffset, inputOffset + inputLength);
    this.valueHexView = new Uint8Array(inputLength);
    for (var i = 0; i < inputLength; i++) {
      this.valueHexView[i] = intBuffer[i] & 0x7F;
      this.blockLength++;
      if ((intBuffer[i] & 0x80) === 0x00) break;
    }
    var tempView = new Uint8Array(this.blockLength);
    for (var _i22 = 0; _i22 < this.blockLength; _i22++) tempView[_i22] = this.valueHexView[_i22];
    this.valueHexView = tempView;
    if ((intBuffer[this.blockLength - 1] & 0x80) !== 0x00) {
      this.error = "End of input reached before message was fully decoded";
      return -1;
    }
    if (this.valueHexView[0] === 0x00) this.warnings.push("Needlessly long format of SID encoding");
    if (this.blockLength <= 8) this.valueDec = utilFromBase(this.valueHexView, 7);else {
      this.isHexOnly = true;
      this.warnings.push("Too big SID for decoding, hex only");
    }
    return inputOffset + this.blockLength;
  };
  _proto24.toBER = function toBER(sizeOnly) {
    if (this.isHexOnly) {
      if (sizeOnly) return new ArrayBuffer(this.valueHexView.byteLength);
      var curView = this.valueHexView;
      var _retView4 = new Uint8Array(this.blockLength);
      for (var i = 0; i < this.blockLength - 1; i++) _retView4[i] = curView[i] | 0x80;
      _retView4[this.blockLength - 1] = curView[this.blockLength - 1];
      return _retView4.buffer;
    }
    var encodedBuf = utilToBase(this.valueDec, 7);
    if (encodedBuf.byteLength === 0) {
      this.error = "Error during encoding SID value";
      return EMPTY_BUFFER$1;
    }
    var retView = new Uint8Array(encodedBuf.byteLength);
    if (!sizeOnly) {
      var encodedView = new Uint8Array(encodedBuf);
      var len = encodedBuf.byteLength - 1;
      for (var _i23 = 0; _i23 < len; _i23++) retView[_i23] = encodedView[_i23] | 0x80;
      retView[len] = encodedView[len];
    }
    return retView.buffer;
  };
  _proto24.toString = function toString() {
    var result = "";
    if (this.isHexOnly) result = Convert.ToHex(this.valueHexView);else {
      result = this.valueDec.toString();
    }
    return result;
  };
  _proto24.toJSON = function toJSON() {
    return Object.assign({}, _HexBlock8.prototype.toJSON.call(this), {
      valueDec: this.valueDec
    });
  };
  return LocalRelativeSidValueBlock;
}(HexBlock(LocalBaseBlock));
LocalRelativeSidValueBlock.NAME = "relativeSidBlock";
var LocalRelativeObjectIdentifierValueBlock = /*#__PURE__*/function (_ValueBlock4) {
  _inheritsLoose(LocalRelativeObjectIdentifierValueBlock, _ValueBlock4);
  function LocalRelativeObjectIdentifierValueBlock(_ref30) {
    var _this25;
    if (_ref30 === void 0) {
      _ref30 = {};
    }
    var _ref31 = _ref30,
      _ref31$value = _ref31.value,
      value = _ref31$value === void 0 ? EMPTY_STRING$1 : _ref31$value,
      parameters = _objectWithoutPropertiesLoose(_ref31, _excluded14);
    _this25 = _ValueBlock4.call(this, parameters) || this;
    _this25.value = [];
    if (value) {
      _this25.fromString(value);
    }
    return _this25;
  }
  var _proto25 = LocalRelativeObjectIdentifierValueBlock.prototype;
  _proto25.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    var resultOffset = inputOffset;
    while (inputLength > 0) {
      var sidBlock = new LocalRelativeSidValueBlock();
      resultOffset = sidBlock.fromBER(inputBuffer, resultOffset, inputLength);
      if (resultOffset === -1) {
        this.blockLength = 0;
        this.error = sidBlock.error;
        return resultOffset;
      }
      this.blockLength += sidBlock.blockLength;
      inputLength -= sidBlock.blockLength;
      this.value.push(sidBlock);
    }
    return resultOffset;
  };
  _proto25.toBER = function toBER(sizeOnly, writer) {
    var retBuffers = [];
    for (var i = 0; i < this.value.length; i++) {
      var valueBuf = this.value[i].toBER(sizeOnly);
      if (valueBuf.byteLength === 0) {
        this.error = this.value[i].error;
        return EMPTY_BUFFER$1;
      }
      retBuffers.push(valueBuf);
    }
    return concat(retBuffers);
  };
  _proto25.fromString = function fromString(string) {
    this.value = [];
    var pos1 = 0;
    var pos2 = 0;
    var sid = "";
    do {
      pos2 = string.indexOf(".", pos1);
      if (pos2 === -1) sid = string.substring(pos1);else sid = string.substring(pos1, pos2);
      pos1 = pos2 + 1;
      var sidBlock = new LocalRelativeSidValueBlock();
      sidBlock.valueDec = parseInt(sid, 10);
      if (isNaN(sidBlock.valueDec)) return true;
      this.value.push(sidBlock);
    } while (pos2 !== -1);
    return true;
  };
  _proto25.toString = function toString() {
    var result = "";
    var isHexOnly = false;
    for (var i = 0; i < this.value.length; i++) {
      isHexOnly = this.value[i].isHexOnly;
      var sidStr = this.value[i].toString();
      if (i !== 0) result = `${result}.`;
      if (isHexOnly) {
        sidStr = `{${sidStr}}`;
        result += sidStr;
      } else result += sidStr;
    }
    return result;
  };
  _proto25.toJSON = function toJSON() {
    var object = Object.assign({}, _ValueBlock4.prototype.toJSON.call(this), {
      value: this.toString(),
      sidArray: []
    });
    for (var i = 0; i < this.value.length; i++) object.sidArray.push(this.value[i].toJSON());
    return object;
  };
  return LocalRelativeObjectIdentifierValueBlock;
}(ValueBlock);
LocalRelativeObjectIdentifierValueBlock.NAME = "RelativeObjectIdentifierValueBlock";
var _a$l;
var RelativeObjectIdentifier = /*#__PURE__*/function (_BaseBlock11) {
  _inheritsLoose(RelativeObjectIdentifier, _BaseBlock11);
  function RelativeObjectIdentifier(parameters) {
    var _this26;
    if (parameters === void 0) {
      parameters = {};
    }
    _this26 = _BaseBlock11.call(this, parameters, LocalRelativeObjectIdentifierValueBlock) || this;
    _this26.idBlock.tagClass = 1;
    _this26.idBlock.tagNumber = 13;
    return _this26;
  }
  var _proto26 = RelativeObjectIdentifier.prototype;
  _proto26.getValue = function getValue() {
    return this.valueBlock.toString();
  };
  _proto26.setValue = function setValue(value) {
    this.valueBlock.fromString(value);
  };
  _proto26.onAsciiEncoding = function onAsciiEncoding() {
    return `${this.constructor.NAME} : ${this.valueBlock.toString() || "empty"}`;
  };
  _proto26.toJSON = function toJSON() {
    return Object.assign({}, _BaseBlock11.prototype.toJSON.call(this), {
      value: this.getValue()
    });
  };
  return RelativeObjectIdentifier;
}(BaseBlock);
_a$l = RelativeObjectIdentifier;
(() => {
  typeStore.RelativeObjectIdentifier = _a$l;
})();
RelativeObjectIdentifier.NAME = "RelativeObjectIdentifier";
var _a$k;
var Sequence = /*#__PURE__*/function (_Constructed) {
  _inheritsLoose(Sequence, _Constructed);
  function Sequence(parameters) {
    var _this27;
    if (parameters === void 0) {
      parameters = {};
    }
    _this27 = _Constructed.call(this, parameters) || this;
    _this27.idBlock.tagClass = 1;
    _this27.idBlock.tagNumber = 16;
    return _this27;
  }
  return Sequence;
}(Constructed);
_a$k = Sequence;
(() => {
  typeStore.Sequence = _a$k;
})();
Sequence.NAME = "SEQUENCE";
var _a$j;
var Set = /*#__PURE__*/function (_Constructed2) {
  _inheritsLoose(Set, _Constructed2);
  function Set(parameters) {
    var _this28;
    if (parameters === void 0) {
      parameters = {};
    }
    _this28 = _Constructed2.call(this, parameters) || this;
    _this28.idBlock.tagClass = 1;
    _this28.idBlock.tagNumber = 17;
    return _this28;
  }
  return Set;
}(Constructed);
_a$j = Set;
(() => {
  typeStore.Set = _a$j;
})();
Set.NAME = "SET";
var LocalStringValueBlock = /*#__PURE__*/function (_HexBlock9) {
  _inheritsLoose(LocalStringValueBlock, _HexBlock9);
  function LocalStringValueBlock(_ref32) {
    var _this29;
    if (_ref32 === void 0) {
      _ref32 = {};
    }
    var _ref33 = _ref32,
      parameters = Object.assign({}, (_objectDestructuringEmpty(_ref33), _ref33));
    _this29 = _HexBlock9.call(this, parameters) || this;
    _this29.isHexOnly = true;
    _this29.value = EMPTY_STRING$1;
    return _this29;
  }
  var _proto27 = LocalStringValueBlock.prototype;
  _proto27.toJSON = function toJSON() {
    return Object.assign({}, _HexBlock9.prototype.toJSON.call(this), {
      value: this.value
    });
  };
  return LocalStringValueBlock;
}(HexBlock(ValueBlock));
LocalStringValueBlock.NAME = "StringValueBlock";
var LocalSimpleStringValueBlock = /*#__PURE__*/function (_LocalStringValueBloc) {
  _inheritsLoose(LocalSimpleStringValueBlock, _LocalStringValueBloc);
  function LocalSimpleStringValueBlock() {
    return _LocalStringValueBloc.apply(this, arguments) || this;
  }
  return LocalSimpleStringValueBlock;
}(LocalStringValueBlock);
LocalSimpleStringValueBlock.NAME = "SimpleStringValueBlock";
var LocalSimpleStringBlock = /*#__PURE__*/function (_BaseStringBlock) {
  _inheritsLoose(LocalSimpleStringBlock, _BaseStringBlock);
  function LocalSimpleStringBlock(_ref34) {
    if (_ref34 === void 0) {
      _ref34 = {};
    }
    var _ref35 = _ref34,
      parameters = Object.assign({}, (_objectDestructuringEmpty(_ref35), _ref35));
    return _BaseStringBlock.call(this, parameters, LocalSimpleStringValueBlock) || this;
  }
  var _proto28 = LocalSimpleStringBlock.prototype;
  _proto28.fromBuffer = function fromBuffer(inputBuffer) {
    this.valueBlock.value = String.fromCharCode.apply(null, BufferSourceConverter.toUint8Array(inputBuffer));
  };
  _proto28.fromString = function fromString(inputString) {
    var strLen = inputString.length;
    var view = this.valueBlock.valueHexView = new Uint8Array(strLen);
    for (var i = 0; i < strLen; i++) view[i] = inputString.charCodeAt(i);
    this.valueBlock.value = inputString;
  };
  return LocalSimpleStringBlock;
}(BaseStringBlock);
LocalSimpleStringBlock.NAME = "SIMPLE STRING";
var LocalUtf8StringValueBlock = /*#__PURE__*/function (_LocalSimpleStringBlo) {
  _inheritsLoose(LocalUtf8StringValueBlock, _LocalSimpleStringBlo);
  function LocalUtf8StringValueBlock() {
    return _LocalSimpleStringBlo.apply(this, arguments) || this;
  }
  var _proto29 = LocalUtf8StringValueBlock.prototype;
  _proto29.fromBuffer = function fromBuffer(inputBuffer) {
    this.valueBlock.valueHexView = BufferSourceConverter.toUint8Array(inputBuffer);
    try {
      this.valueBlock.value = Convert.ToUtf8String(inputBuffer);
    } catch (ex) {
      this.warnings.push(`Error during "decodeURIComponent": ${ex}, using raw string`);
      this.valueBlock.value = Convert.ToBinary(inputBuffer);
    }
  };
  _proto29.fromString = function fromString(inputString) {
    this.valueBlock.valueHexView = new Uint8Array(Convert.FromUtf8String(inputString));
    this.valueBlock.value = inputString;
  };
  return LocalUtf8StringValueBlock;
}(LocalSimpleStringBlock);
LocalUtf8StringValueBlock.NAME = "Utf8StringValueBlock";
var _a$i;
var Utf8String = /*#__PURE__*/function (_LocalUtf8StringValue) {
  _inheritsLoose(Utf8String, _LocalUtf8StringValue);
  function Utf8String(parameters) {
    var _this30;
    if (parameters === void 0) {
      parameters = {};
    }
    _this30 = _LocalUtf8StringValue.call(this, parameters) || this;
    _this30.idBlock.tagClass = 1;
    _this30.idBlock.tagNumber = 12;
    return _this30;
  }
  return Utf8String;
}(LocalUtf8StringValueBlock);
_a$i = Utf8String;
(() => {
  typeStore.Utf8String = _a$i;
})();
Utf8String.NAME = "UTF8String";
var LocalBmpStringValueBlock = /*#__PURE__*/function (_LocalSimpleStringBlo2) {
  _inheritsLoose(LocalBmpStringValueBlock, _LocalSimpleStringBlo2);
  function LocalBmpStringValueBlock() {
    return _LocalSimpleStringBlo2.apply(this, arguments) || this;
  }
  var _proto30 = LocalBmpStringValueBlock.prototype;
  _proto30.fromBuffer = function fromBuffer(inputBuffer) {
    this.valueBlock.value = Convert.ToUtf16String(inputBuffer);
    this.valueBlock.valueHexView = BufferSourceConverter.toUint8Array(inputBuffer);
  };
  _proto30.fromString = function fromString(inputString) {
    this.valueBlock.value = inputString;
    this.valueBlock.valueHexView = new Uint8Array(Convert.FromUtf16String(inputString));
  };
  return LocalBmpStringValueBlock;
}(LocalSimpleStringBlock);
LocalBmpStringValueBlock.NAME = "BmpStringValueBlock";
var _a$h;
var BmpString = /*#__PURE__*/function (_LocalBmpStringValueB) {
  _inheritsLoose(BmpString, _LocalBmpStringValueB);
  function BmpString(_ref36) {
    var _this31;
    if (_ref36 === void 0) {
      _ref36 = {};
    }
    var _ref37 = _ref36,
      parameters = Object.assign({}, (_objectDestructuringEmpty(_ref37), _ref37));
    _this31 = _LocalBmpStringValueB.call(this, parameters) || this;
    _this31.idBlock.tagClass = 1;
    _this31.idBlock.tagNumber = 30;
    return _this31;
  }
  return BmpString;
}(LocalBmpStringValueBlock);
_a$h = BmpString;
(() => {
  typeStore.BmpString = _a$h;
})();
BmpString.NAME = "BMPString";
var LocalUniversalStringValueBlock = /*#__PURE__*/function (_LocalSimpleStringBlo3) {
  _inheritsLoose(LocalUniversalStringValueBlock, _LocalSimpleStringBlo3);
  function LocalUniversalStringValueBlock() {
    return _LocalSimpleStringBlo3.apply(this, arguments) || this;
  }
  var _proto31 = LocalUniversalStringValueBlock.prototype;
  _proto31.fromBuffer = function fromBuffer(inputBuffer) {
    var copyBuffer = ArrayBuffer.isView(inputBuffer) ? inputBuffer.slice().buffer : inputBuffer.slice(0);
    var valueView = new Uint8Array(copyBuffer);
    for (var i = 0; i < valueView.length; i += 4) {
      valueView[i] = valueView[i + 3];
      valueView[i + 1] = valueView[i + 2];
      valueView[i + 2] = 0x00;
      valueView[i + 3] = 0x00;
    }
    this.valueBlock.value = String.fromCharCode.apply(null, new Uint32Array(copyBuffer));
  };
  _proto31.fromString = function fromString(inputString) {
    var strLength = inputString.length;
    var valueHexView = this.valueBlock.valueHexView = new Uint8Array(strLength * 4);
    for (var i = 0; i < strLength; i++) {
      var codeBuf = utilToBase(inputString.charCodeAt(i), 8);
      var codeView = new Uint8Array(codeBuf);
      if (codeView.length > 4) continue;
      var dif = 4 - codeView.length;
      for (var j = codeView.length - 1; j >= 0; j--) valueHexView[i * 4 + j + dif] = codeView[j];
    }
    this.valueBlock.value = inputString;
  };
  return LocalUniversalStringValueBlock;
}(LocalSimpleStringBlock);
LocalUniversalStringValueBlock.NAME = "UniversalStringValueBlock";
var _a$g;
var UniversalString = /*#__PURE__*/function (_LocalUniversalString) {
  _inheritsLoose(UniversalString, _LocalUniversalString);
  function UniversalString(_ref38) {
    var _this32;
    if (_ref38 === void 0) {
      _ref38 = {};
    }
    var _ref39 = _ref38,
      parameters = Object.assign({}, (_objectDestructuringEmpty(_ref39), _ref39));
    _this32 = _LocalUniversalString.call(this, parameters) || this;
    _this32.idBlock.tagClass = 1;
    _this32.idBlock.tagNumber = 28;
    return _this32;
  }
  return UniversalString;
}(LocalUniversalStringValueBlock);
_a$g = UniversalString;
(() => {
  typeStore.UniversalString = _a$g;
})();
UniversalString.NAME = "UniversalString";
var _a$f;
var NumericString = /*#__PURE__*/function (_LocalSimpleStringBlo4) {
  _inheritsLoose(NumericString, _LocalSimpleStringBlo4);
  function NumericString(parameters) {
    var _this33;
    if (parameters === void 0) {
      parameters = {};
    }
    _this33 = _LocalSimpleStringBlo4.call(this, parameters) || this;
    _this33.idBlock.tagClass = 1;
    _this33.idBlock.tagNumber = 18;
    return _this33;
  }
  return NumericString;
}(LocalSimpleStringBlock);
_a$f = NumericString;
(() => {
  typeStore.NumericString = _a$f;
})();
NumericString.NAME = "NumericString";
var _a$e;
var PrintableString = /*#__PURE__*/function (_LocalSimpleStringBlo5) {
  _inheritsLoose(PrintableString, _LocalSimpleStringBlo5);
  function PrintableString(parameters) {
    var _this34;
    if (parameters === void 0) {
      parameters = {};
    }
    _this34 = _LocalSimpleStringBlo5.call(this, parameters) || this;
    _this34.idBlock.tagClass = 1;
    _this34.idBlock.tagNumber = 19;
    return _this34;
  }
  return PrintableString;
}(LocalSimpleStringBlock);
_a$e = PrintableString;
(() => {
  typeStore.PrintableString = _a$e;
})();
PrintableString.NAME = "PrintableString";
var _a$d;
var TeletexString = /*#__PURE__*/function (_LocalSimpleStringBlo6) {
  _inheritsLoose(TeletexString, _LocalSimpleStringBlo6);
  function TeletexString(parameters) {
    var _this35;
    if (parameters === void 0) {
      parameters = {};
    }
    _this35 = _LocalSimpleStringBlo6.call(this, parameters) || this;
    _this35.idBlock.tagClass = 1;
    _this35.idBlock.tagNumber = 20;
    return _this35;
  }
  return TeletexString;
}(LocalSimpleStringBlock);
_a$d = TeletexString;
(() => {
  typeStore.TeletexString = _a$d;
})();
TeletexString.NAME = "TeletexString";
var _a$c;
var VideotexString = /*#__PURE__*/function (_LocalSimpleStringBlo7) {
  _inheritsLoose(VideotexString, _LocalSimpleStringBlo7);
  function VideotexString(parameters) {
    var _this36;
    if (parameters === void 0) {
      parameters = {};
    }
    _this36 = _LocalSimpleStringBlo7.call(this, parameters) || this;
    _this36.idBlock.tagClass = 1;
    _this36.idBlock.tagNumber = 21;
    return _this36;
  }
  return VideotexString;
}(LocalSimpleStringBlock);
_a$c = VideotexString;
(() => {
  typeStore.VideotexString = _a$c;
})();
VideotexString.NAME = "VideotexString";
var _a$b;
var IA5String = /*#__PURE__*/function (_LocalSimpleStringBlo8) {
  _inheritsLoose(IA5String, _LocalSimpleStringBlo8);
  function IA5String(parameters) {
    var _this37;
    if (parameters === void 0) {
      parameters = {};
    }
    _this37 = _LocalSimpleStringBlo8.call(this, parameters) || this;
    _this37.idBlock.tagClass = 1;
    _this37.idBlock.tagNumber = 22;
    return _this37;
  }
  return IA5String;
}(LocalSimpleStringBlock);
_a$b = IA5String;
(() => {
  typeStore.IA5String = _a$b;
})();
IA5String.NAME = "IA5String";
var _a$a;
var GraphicString = /*#__PURE__*/function (_LocalSimpleStringBlo9) {
  _inheritsLoose(GraphicString, _LocalSimpleStringBlo9);
  function GraphicString(parameters) {
    var _this38;
    if (parameters === void 0) {
      parameters = {};
    }
    _this38 = _LocalSimpleStringBlo9.call(this, parameters) || this;
    _this38.idBlock.tagClass = 1;
    _this38.idBlock.tagNumber = 25;
    return _this38;
  }
  return GraphicString;
}(LocalSimpleStringBlock);
_a$a = GraphicString;
(() => {
  typeStore.GraphicString = _a$a;
})();
GraphicString.NAME = "GraphicString";
var _a$9;
var VisibleString = /*#__PURE__*/function (_LocalSimpleStringBlo10) {
  _inheritsLoose(VisibleString, _LocalSimpleStringBlo10);
  function VisibleString(parameters) {
    var _this39;
    if (parameters === void 0) {
      parameters = {};
    }
    _this39 = _LocalSimpleStringBlo10.call(this, parameters) || this;
    _this39.idBlock.tagClass = 1;
    _this39.idBlock.tagNumber = 26;
    return _this39;
  }
  return VisibleString;
}(LocalSimpleStringBlock);
_a$9 = VisibleString;
(() => {
  typeStore.VisibleString = _a$9;
})();
VisibleString.NAME = "VisibleString";
var _a$8;
var GeneralString = /*#__PURE__*/function (_LocalSimpleStringBlo11) {
  _inheritsLoose(GeneralString, _LocalSimpleStringBlo11);
  function GeneralString(parameters) {
    var _this40;
    if (parameters === void 0) {
      parameters = {};
    }
    _this40 = _LocalSimpleStringBlo11.call(this, parameters) || this;
    _this40.idBlock.tagClass = 1;
    _this40.idBlock.tagNumber = 27;
    return _this40;
  }
  return GeneralString;
}(LocalSimpleStringBlock);
_a$8 = GeneralString;
(() => {
  typeStore.GeneralString = _a$8;
})();
GeneralString.NAME = "GeneralString";
var _a$7;
var CharacterString = /*#__PURE__*/function (_LocalSimpleStringBlo12) {
  _inheritsLoose(CharacterString, _LocalSimpleStringBlo12);
  function CharacterString(parameters) {
    var _this41;
    if (parameters === void 0) {
      parameters = {};
    }
    _this41 = _LocalSimpleStringBlo12.call(this, parameters) || this;
    _this41.idBlock.tagClass = 1;
    _this41.idBlock.tagNumber = 29;
    return _this41;
  }
  return CharacterString;
}(LocalSimpleStringBlock);
_a$7 = CharacterString;
(() => {
  typeStore.CharacterString = _a$7;
})();
CharacterString.NAME = "CharacterString";
var _a$6;
var UTCTime = /*#__PURE__*/function (_VisibleString) {
  _inheritsLoose(UTCTime, _VisibleString);
  function UTCTime(_ref40) {
    var _this42;
    if (_ref40 === void 0) {
      _ref40 = {};
    }
    var _ref41 = _ref40,
      value = _ref41.value,
      valueDate = _ref41.valueDate,
      parameters = _objectWithoutPropertiesLoose(_ref41, _excluded15);
    _this42 = _VisibleString.call(this, parameters) || this;
    _this42.year = 0;
    _this42.month = 0;
    _this42.day = 0;
    _this42.hour = 0;
    _this42.minute = 0;
    _this42.second = 0;
    if (value) {
      _this42.fromString(value);
      _this42.valueBlock.valueHexView = new Uint8Array(value.length);
      for (var i = 0; i < value.length; i++) _this42.valueBlock.valueHexView[i] = value.charCodeAt(i);
    }
    if (valueDate) {
      _this42.fromDate(valueDate);
      _this42.valueBlock.valueHexView = new Uint8Array(_this42.toBuffer());
    }
    _this42.idBlock.tagClass = 1;
    _this42.idBlock.tagNumber = 23;
    return _this42;
  }
  var _proto32 = UTCTime.prototype;
  _proto32.fromBuffer = function fromBuffer(inputBuffer) {
    this.fromString(String.fromCharCode.apply(null, BufferSourceConverter.toUint8Array(inputBuffer)));
  };
  _proto32.toBuffer = function toBuffer() {
    var str = this.toString();
    var buffer = new ArrayBuffer(str.length);
    var view = new Uint8Array(buffer);
    for (var i = 0; i < str.length; i++) view[i] = str.charCodeAt(i);
    return buffer;
  };
  _proto32.fromDate = function fromDate(inputDate) {
    this.year = inputDate.getUTCFullYear();
    this.month = inputDate.getUTCMonth() + 1;
    this.day = inputDate.getUTCDate();
    this.hour = inputDate.getUTCHours();
    this.minute = inputDate.getUTCMinutes();
    this.second = inputDate.getUTCSeconds();
  };
  _proto32.toDate = function toDate() {
    return new Date(Date.UTC(this.year, this.month - 1, this.day, this.hour, this.minute, this.second));
  };
  _proto32.fromString = function fromString(inputString) {
    var parser = /(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})Z/ig;
    var parserArray = parser.exec(inputString);
    if (parserArray === null) {
      this.error = "Wrong input string for conversion";
      return;
    }
    var year = parseInt(parserArray[1], 10);
    if (year >= 50) this.year = 1900 + year;else this.year = 2000 + year;
    this.month = parseInt(parserArray[2], 10);
    this.day = parseInt(parserArray[3], 10);
    this.hour = parseInt(parserArray[4], 10);
    this.minute = parseInt(parserArray[5], 10);
    this.second = parseInt(parserArray[6], 10);
  };
  _proto32.toString = function toString(encoding) {
    if (encoding === void 0) {
      encoding = "iso";
    }
    if (encoding === "iso") {
      var outputArray = new Array(7);
      outputArray[0] = padNumber(this.year < 2000 ? this.year - 1900 : this.year - 2000, 2);
      outputArray[1] = padNumber(this.month, 2);
      outputArray[2] = padNumber(this.day, 2);
      outputArray[3] = padNumber(this.hour, 2);
      outputArray[4] = padNumber(this.minute, 2);
      outputArray[5] = padNumber(this.second, 2);
      outputArray[6] = "Z";
      return outputArray.join("");
    }
    return _VisibleString.prototype.toString.call(this, encoding);
  };
  _proto32.onAsciiEncoding = function onAsciiEncoding() {
    return `${this.constructor.NAME} : ${this.toDate().toISOString()}`;
  };
  _proto32.toJSON = function toJSON() {
    return Object.assign({}, _VisibleString.prototype.toJSON.call(this), {
      year: this.year,
      month: this.month,
      day: this.day,
      hour: this.hour,
      minute: this.minute,
      second: this.second
    });
  };
  return UTCTime;
}(VisibleString);
_a$6 = UTCTime;
(() => {
  typeStore.UTCTime = _a$6;
})();
UTCTime.NAME = "UTCTime";
var _a$5;
var GeneralizedTime = /*#__PURE__*/function (_UTCTime) {
  _inheritsLoose(GeneralizedTime, _UTCTime);
  function GeneralizedTime(parameters) {
    var _this43;
    if (parameters === void 0) {
      parameters = {};
    }
    var _b;
    _this43 = _UTCTime.call(this, parameters) || this;
    (_b = _this43.millisecond) !== null && _b !== void 0 ? _b : _this43.millisecond = 0;
    _this43.idBlock.tagClass = 1;
    _this43.idBlock.tagNumber = 24;
    return _this43;
  }
  var _proto33 = GeneralizedTime.prototype;
  _proto33.fromDate = function fromDate(inputDate) {
    _UTCTime.prototype.fromDate.call(this, inputDate);
    this.millisecond = inputDate.getUTCMilliseconds();
  };
  _proto33.toDate = function toDate() {
    return new Date(Date.UTC(this.year, this.month - 1, this.day, this.hour, this.minute, this.second, this.millisecond));
  };
  _proto33.fromString = function fromString(inputString) {
    var isUTC = false;
    var timeString = "";
    var dateTimeString = "";
    var fractionPart = 0;
    var parser;
    var hourDifference = 0;
    var minuteDifference = 0;
    if (inputString[inputString.length - 1] === "Z") {
      timeString = inputString.substring(0, inputString.length - 1);
      isUTC = true;
    } else {
      var number = new Number(inputString[inputString.length - 1]);
      if (isNaN(number.valueOf())) throw new Error("Wrong input string for conversion");
      timeString = inputString;
    }
    if (isUTC) {
      if (timeString.indexOf("+") !== -1) throw new Error("Wrong input string for conversion");
      if (timeString.indexOf("-") !== -1) throw new Error("Wrong input string for conversion");
    } else {
      var multiplier = 1;
      var differencePosition = timeString.indexOf("+");
      var differenceString = "";
      if (differencePosition === -1) {
        differencePosition = timeString.indexOf("-");
        multiplier = -1;
      }
      if (differencePosition !== -1) {
        differenceString = timeString.substring(differencePosition + 1);
        timeString = timeString.substring(0, differencePosition);
        if (differenceString.length !== 2 && differenceString.length !== 4) throw new Error("Wrong input string for conversion");
        var _number = parseInt(differenceString.substring(0, 2), 10);
        if (isNaN(_number.valueOf())) throw new Error("Wrong input string for conversion");
        hourDifference = multiplier * _number;
        if (differenceString.length === 4) {
          _number = parseInt(differenceString.substring(2, 4), 10);
          if (isNaN(_number.valueOf())) throw new Error("Wrong input string for conversion");
          minuteDifference = multiplier * _number;
        }
      }
    }
    var fractionPointPosition = timeString.indexOf(".");
    if (fractionPointPosition === -1) fractionPointPosition = timeString.indexOf(",");
    if (fractionPointPosition !== -1) {
      var fractionPartCheck = new Number(`0${timeString.substring(fractionPointPosition)}`);
      if (isNaN(fractionPartCheck.valueOf())) throw new Error("Wrong input string for conversion");
      fractionPart = fractionPartCheck.valueOf();
      dateTimeString = timeString.substring(0, fractionPointPosition);
    } else dateTimeString = timeString;
    switch (true) {
      case dateTimeString.length === 8:
        parser = /(\d{4})(\d{2})(\d{2})/ig;
        if (fractionPointPosition !== -1) throw new Error("Wrong input string for conversion");
        break;
      case dateTimeString.length === 10:
        parser = /(\d{4})(\d{2})(\d{2})(\d{2})/ig;
        if (fractionPointPosition !== -1) {
          var fractionResult = 60 * fractionPart;
          this.minute = Math.floor(fractionResult);
          fractionResult = 60 * (fractionResult - this.minute);
          this.second = Math.floor(fractionResult);
          fractionResult = 1000 * (fractionResult - this.second);
          this.millisecond = Math.floor(fractionResult);
        }
        break;
      case dateTimeString.length === 12:
        parser = /(\d{4})(\d{2})(\d{2})(\d{2})(\d{2})/ig;
        if (fractionPointPosition !== -1) {
          var _fractionResult = 60 * fractionPart;
          this.second = Math.floor(_fractionResult);
          _fractionResult = 1000 * (_fractionResult - this.second);
          this.millisecond = Math.floor(_fractionResult);
        }
        break;
      case dateTimeString.length === 14:
        parser = /(\d{4})(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})/ig;
        if (fractionPointPosition !== -1) {
          var _fractionResult2 = 1000 * fractionPart;
          this.millisecond = Math.floor(_fractionResult2);
        }
        break;
      default:
        throw new Error("Wrong input string for conversion");
    }
    var parserArray = parser.exec(dateTimeString);
    if (parserArray === null) throw new Error("Wrong input string for conversion");
    for (var j = 1; j < parserArray.length; j++) {
      switch (j) {
        case 1:
          this.year = parseInt(parserArray[j], 10);
          break;
        case 2:
          this.month = parseInt(parserArray[j], 10);
          break;
        case 3:
          this.day = parseInt(parserArray[j], 10);
          break;
        case 4:
          this.hour = parseInt(parserArray[j], 10) + hourDifference;
          break;
        case 5:
          this.minute = parseInt(parserArray[j], 10) + minuteDifference;
          break;
        case 6:
          this.second = parseInt(parserArray[j], 10);
          break;
        default:
          throw new Error("Wrong input string for conversion");
      }
    }
    if (isUTC === false) {
      var tempDate = new Date(this.year, this.month, this.day, this.hour, this.minute, this.second, this.millisecond);
      this.year = tempDate.getUTCFullYear();
      this.month = tempDate.getUTCMonth();
      this.day = tempDate.getUTCDay();
      this.hour = tempDate.getUTCHours();
      this.minute = tempDate.getUTCMinutes();
      this.second = tempDate.getUTCSeconds();
      this.millisecond = tempDate.getUTCMilliseconds();
    }
  };
  _proto33.toString = function toString(encoding) {
    if (encoding === void 0) {
      encoding = "iso";
    }
    if (encoding === "iso") {
      var outputArray = [];
      outputArray.push(padNumber(this.year, 4));
      outputArray.push(padNumber(this.month, 2));
      outputArray.push(padNumber(this.day, 2));
      outputArray.push(padNumber(this.hour, 2));
      outputArray.push(padNumber(this.minute, 2));
      outputArray.push(padNumber(this.second, 2));
      if (this.millisecond !== 0) {
        outputArray.push(".");
        outputArray.push(padNumber(this.millisecond, 3));
      }
      outputArray.push("Z");
      return outputArray.join("");
    }
    return _UTCTime.prototype.toString.call(this, encoding);
  };
  _proto33.toJSON = function toJSON() {
    return Object.assign({}, _UTCTime.prototype.toJSON.call(this), {
      millisecond: this.millisecond
    });
  };
  return GeneralizedTime;
}(UTCTime);
_a$5 = GeneralizedTime;
(() => {
  typeStore.GeneralizedTime = _a$5;
})();
GeneralizedTime.NAME = "GeneralizedTime";
var _a$4;
var DATE = /*#__PURE__*/function (_Utf8String) {
  _inheritsLoose(DATE, _Utf8String);
  function DATE(parameters) {
    var _this44;
    if (parameters === void 0) {
      parameters = {};
    }
    _this44 = _Utf8String.call(this, parameters) || this;
    _this44.idBlock.tagClass = 1;
    _this44.idBlock.tagNumber = 31;
    return _this44;
  }
  return DATE;
}(Utf8String);
_a$4 = DATE;
(() => {
  typeStore.DATE = _a$4;
})();
DATE.NAME = "DATE";
var _a$3;
var TimeOfDay = /*#__PURE__*/function (_Utf8String2) {
  _inheritsLoose(TimeOfDay, _Utf8String2);
  function TimeOfDay(parameters) {
    var _this45;
    if (parameters === void 0) {
      parameters = {};
    }
    _this45 = _Utf8String2.call(this, parameters) || this;
    _this45.idBlock.tagClass = 1;
    _this45.idBlock.tagNumber = 32;
    return _this45;
  }
  return TimeOfDay;
}(Utf8String);
_a$3 = TimeOfDay;
(() => {
  typeStore.TimeOfDay = _a$3;
})();
TimeOfDay.NAME = "TimeOfDay";
var _a$2;
var DateTime = /*#__PURE__*/function (_Utf8String3) {
  _inheritsLoose(DateTime, _Utf8String3);
  function DateTime(parameters) {
    var _this46;
    if (parameters === void 0) {
      parameters = {};
    }
    _this46 = _Utf8String3.call(this, parameters) || this;
    _this46.idBlock.tagClass = 1;
    _this46.idBlock.tagNumber = 33;
    return _this46;
  }
  return DateTime;
}(Utf8String);
_a$2 = DateTime;
(() => {
  typeStore.DateTime = _a$2;
})();
DateTime.NAME = "DateTime";
var _a$1;
var Duration = /*#__PURE__*/function (_Utf8String4) {
  _inheritsLoose(Duration, _Utf8String4);
  function Duration(parameters) {
    var _this47;
    if (parameters === void 0) {
      parameters = {};
    }
    _this47 = _Utf8String4.call(this, parameters) || this;
    _this47.idBlock.tagClass = 1;
    _this47.idBlock.tagNumber = 34;
    return _this47;
  }
  return Duration;
}(Utf8String);
_a$1 = Duration;
(() => {
  typeStore.Duration = _a$1;
})();
Duration.NAME = "Duration";
var _a$x;
var TIME = /*#__PURE__*/function (_Utf8String5) {
  _inheritsLoose(TIME, _Utf8String5);
  function TIME(parameters) {
    var _this48;
    if (parameters === void 0) {
      parameters = {};
    }
    _this48 = _Utf8String5.call(this, parameters) || this;
    _this48.idBlock.tagClass = 1;
    _this48.idBlock.tagNumber = 14;
    return _this48;
  }
  return TIME;
}(Utf8String);
_a$x = TIME;
(() => {
  typeStore.TIME = _a$x;
})();
TIME.NAME = "TIME";
var Any = function Any(_temp4) {
  var _ref42 = _temp4 === void 0 ? {} : _temp4,
    _ref42$name = _ref42.name,
    name = _ref42$name === void 0 ? EMPTY_STRING$1 : _ref42$name,
    _ref42$optional = _ref42.optional,
    optional = _ref42$optional === void 0 ? false : _ref42$optional;
  this.name = name;
  this.optional = optional;
};
var Choice = /*#__PURE__*/function (_Any) {
  _inheritsLoose(Choice, _Any);
  function Choice(_ref43) {
    var _this49;
    if (_ref43 === void 0) {
      _ref43 = {};
    }
    var _ref44 = _ref43,
      _ref44$value = _ref44.value,
      value = _ref44$value === void 0 ? [] : _ref44$value,
      parameters = _objectWithoutPropertiesLoose(_ref44, _excluded16);
    _this49 = _Any.call(this, parameters) || this;
    _this49.value = value;
    return _this49;
  }
  return Choice;
}(Any);
var Repeated = /*#__PURE__*/function (_Any2) {
  _inheritsLoose(Repeated, _Any2);
  function Repeated(_ref45) {
    var _this50;
    if (_ref45 === void 0) {
      _ref45 = {};
    }
    var _ref46 = _ref45,
      _ref46$value = _ref46.value,
      value = _ref46$value === void 0 ? new Any() : _ref46$value,
      _ref46$local = _ref46.local,
      local = _ref46$local === void 0 ? false : _ref46$local,
      parameters = _objectWithoutPropertiesLoose(_ref46, _excluded17);
    _this50 = _Any2.call(this, parameters) || this;
    _this50.value = value;
    _this50.local = local;
    return _this50;
  }
  return Repeated;
}(Any);
var RawData = /*#__PURE__*/function () {
  function RawData(_temp5) {
    var _ref47 = _temp5 === void 0 ? {} : _temp5,
      _ref47$data = _ref47.data,
      data = _ref47$data === void 0 ? EMPTY_VIEW : _ref47$data;
    this.dataView = BufferSourceConverter.toUint8Array(data);
  }
  var _proto34 = RawData.prototype;
  _proto34.fromBER = function fromBER(inputBuffer, inputOffset, inputLength) {
    var endLength = inputOffset + inputLength;
    this.dataView = BufferSourceConverter.toUint8Array(inputBuffer).subarray(inputOffset, endLength);
    return endLength;
  };
  _proto34.toBER = function toBER(sizeOnly) {
    return this.dataView.slice().buffer;
  };
  _createClass(RawData, [{
    key: "data",
    get: function () {
      return this.dataView.slice().buffer;
    },
    set: function (value) {
      this.dataView = BufferSourceConverter.toUint8Array(value);
    }
  }]);
  return RawData;
}();
function compareSchema(root, inputData, inputSchema) {
  if (inputSchema instanceof Choice) {
    for (var j = 0; j < inputSchema.value.length; j++) {
      var result = compareSchema(root, inputData, inputSchema.value[j]);
      if (result.verified) {
        return {
          verified: true,
          result: root
        };
      }
    }
    {
      var _result = {
        verified: false,
        result: {
          error: "Wrong values for Choice type"
        }
      };
      if (inputSchema.hasOwnProperty(NAME)) _result.name = inputSchema.name;
      return _result;
    }
  }
  if (inputSchema instanceof Any) {
    if (inputSchema.hasOwnProperty(NAME)) root[inputSchema.name] = inputData;
    return {
      verified: true,
      result: root
    };
  }
  if (root instanceof Object === false) {
    return {
      verified: false,
      result: {
        error: "Wrong root object"
      }
    };
  }
  if (inputData instanceof Object === false) {
    return {
      verified: false,
      result: {
        error: "Wrong ASN.1 data"
      }
    };
  }
  if (inputSchema instanceof Object === false) {
    return {
      verified: false,
      result: {
        error: "Wrong ASN.1 schema"
      }
    };
  }
  if (ID_BLOCK in inputSchema === false) {
    return {
      verified: false,
      result: {
        error: "Wrong ASN.1 schema"
      }
    };
  }
  if (FROM_BER in inputSchema.idBlock === false) {
    return {
      verified: false,
      result: {
        error: "Wrong ASN.1 schema"
      }
    };
  }
  if (TO_BER in inputSchema.idBlock === false) {
    return {
      verified: false,
      result: {
        error: "Wrong ASN.1 schema"
      }
    };
  }
  var encodedId = inputSchema.idBlock.toBER(false);
  if (encodedId.byteLength === 0) {
    return {
      verified: false,
      result: {
        error: "Error encoding idBlock for ASN.1 schema"
      }
    };
  }
  var decodedOffset = inputSchema.idBlock.fromBER(encodedId, 0, encodedId.byteLength);
  if (decodedOffset === -1) {
    return {
      verified: false,
      result: {
        error: "Error decoding idBlock for ASN.1 schema"
      }
    };
  }
  if (inputSchema.idBlock.hasOwnProperty(TAG_CLASS) === false) {
    return {
      verified: false,
      result: {
        error: "Wrong ASN.1 schema"
      }
    };
  }
  if (inputSchema.idBlock.tagClass !== inputData.idBlock.tagClass) {
    return {
      verified: false,
      result: root
    };
  }
  if (inputSchema.idBlock.hasOwnProperty(TAG_NUMBER) === false) {
    return {
      verified: false,
      result: {
        error: "Wrong ASN.1 schema"
      }
    };
  }
  if (inputSchema.idBlock.tagNumber !== inputData.idBlock.tagNumber) {
    return {
      verified: false,
      result: root
    };
  }
  if (inputSchema.idBlock.hasOwnProperty(IS_CONSTRUCTED) === false) {
    return {
      verified: false,
      result: {
        error: "Wrong ASN.1 schema"
      }
    };
  }
  if (inputSchema.idBlock.isConstructed !== inputData.idBlock.isConstructed) {
    return {
      verified: false,
      result: root
    };
  }
  if (!(IS_HEX_ONLY in inputSchema.idBlock)) {
    return {
      verified: false,
      result: {
        error: "Wrong ASN.1 schema"
      }
    };
  }
  if (inputSchema.idBlock.isHexOnly !== inputData.idBlock.isHexOnly) {
    return {
      verified: false,
      result: root
    };
  }
  if (inputSchema.idBlock.isHexOnly) {
    if (VALUE_HEX_VIEW in inputSchema.idBlock === false) {
      return {
        verified: false,
        result: {
          error: "Wrong ASN.1 schema"
        }
      };
    }
    var schemaView = inputSchema.idBlock.valueHexView;
    var asn1View = inputData.idBlock.valueHexView;
    if (schemaView.length !== asn1View.length) {
      return {
        verified: false,
        result: root
      };
    }
    for (var i = 0; i < schemaView.length; i++) {
      if (schemaView[i] !== asn1View[1]) {
        return {
          verified: false,
          result: root
        };
      }
    }
  }
  if (inputSchema.name) {
    inputSchema.name = inputSchema.name.replace(/^\s+|\s+$/g, EMPTY_STRING$1);
    if (inputSchema.name) root[inputSchema.name] = inputData;
  }
  if (inputSchema instanceof typeStore.Constructed) {
    var admission = 0;
    var _result2 = {
      verified: false,
      result: {
        error: "Unknown error"
      }
    };
    var maxLength = inputSchema.valueBlock.value.length;
    if (maxLength > 0) {
      if (inputSchema.valueBlock.value[0] instanceof Repeated) {
        maxLength = inputData.valueBlock.value.length;
      }
    }
    if (maxLength === 0) {
      return {
        verified: true,
        result: root
      };
    }
    if (inputData.valueBlock.value.length === 0 && inputSchema.valueBlock.value.length !== 0) {
      var _optional = true;
      for (var _i24 = 0; _i24 < inputSchema.valueBlock.value.length; _i24++) _optional = _optional && (inputSchema.valueBlock.value[_i24].optional || false);
      if (_optional) {
        return {
          verified: true,
          result: root
        };
      }
      if (inputSchema.name) {
        inputSchema.name = inputSchema.name.replace(/^\s+|\s+$/g, EMPTY_STRING$1);
        if (inputSchema.name) delete root[inputSchema.name];
      }
      root.error = "Inconsistent object length";
      return {
        verified: false,
        result: root
      };
    }
    for (var _i25 = 0; _i25 < maxLength; _i25++) {
      if (_i25 - admission >= inputData.valueBlock.value.length) {
        if (inputSchema.valueBlock.value[_i25].optional === false) {
          var _result3 = {
            verified: false,
            result: root
          };
          root.error = "Inconsistent length between ASN.1 data and schema";
          if (inputSchema.name) {
            inputSchema.name = inputSchema.name.replace(/^\s+|\s+$/g, EMPTY_STRING$1);
            if (inputSchema.name) {
              delete root[inputSchema.name];
              _result3.name = inputSchema.name;
            }
          }
          return _result3;
        }
      } else {
        if (inputSchema.valueBlock.value[0] instanceof Repeated) {
          _result2 = compareSchema(root, inputData.valueBlock.value[_i25], inputSchema.valueBlock.value[0].value);
          if (_result2.verified === false) {
            if (inputSchema.valueBlock.value[0].optional) admission++;else {
              if (inputSchema.name) {
                inputSchema.name = inputSchema.name.replace(/^\s+|\s+$/g, EMPTY_STRING$1);
                if (inputSchema.name) delete root[inputSchema.name];
              }
              return _result2;
            }
          }
          if (NAME in inputSchema.valueBlock.value[0] && inputSchema.valueBlock.value[0].name.length > 0) {
            var arrayRoot = {};
            if (LOCAL in inputSchema.valueBlock.value[0] && inputSchema.valueBlock.value[0].local) arrayRoot = inputData;else arrayRoot = root;
            if (typeof arrayRoot[inputSchema.valueBlock.value[0].name] === "undefined") arrayRoot[inputSchema.valueBlock.value[0].name] = [];
            arrayRoot[inputSchema.valueBlock.value[0].name].push(inputData.valueBlock.value[_i25]);
          }
        } else {
          _result2 = compareSchema(root, inputData.valueBlock.value[_i25 - admission], inputSchema.valueBlock.value[_i25]);
          if (_result2.verified === false) {
            if (inputSchema.valueBlock.value[_i25].optional) admission++;else {
              if (inputSchema.name) {
                inputSchema.name = inputSchema.name.replace(/^\s+|\s+$/g, EMPTY_STRING$1);
                if (inputSchema.name) delete root[inputSchema.name];
              }
              return _result2;
            }
          }
        }
      }
    }
    if (_result2.verified === false) {
      var _result4 = {
        verified: false,
        result: root
      };
      if (inputSchema.name) {
        inputSchema.name = inputSchema.name.replace(/^\s+|\s+$/g, EMPTY_STRING$1);
        if (inputSchema.name) {
          delete root[inputSchema.name];
          _result4.name = inputSchema.name;
        }
      }
      return _result4;
    }
    return {
      verified: true,
      result: root
    };
  }
  if (inputSchema.primitiveSchema && VALUE_HEX_VIEW in inputData.valueBlock) {
    var asn1 = localFromBER(inputData.valueBlock.valueHexView);
    if (asn1.offset === -1) {
      var _result5 = {
        verified: false,
        result: asn1.result
      };
      if (inputSchema.name) {
        inputSchema.name = inputSchema.name.replace(/^\s+|\s+$/g, EMPTY_STRING$1);
        if (inputSchema.name) {
          delete root[inputSchema.name];
          _result5.name = inputSchema.name;
        }
      }
      return _result5;
    }
    return compareSchema(root, asn1.result, inputSchema.primitiveSchema);
  }
  return {
    verified: true,
    result: root
  };
}

var ByteStream = /*#__PURE__*/function () {
  function ByteStream(parameters) {
    if (parameters === void 0) {
      parameters = {};
    }
    if ("view" in parameters) {
      this.fromUint8Array(parameters.view);
    } else if ("buffer" in parameters) {
      this.fromArrayBuffer(parameters.buffer);
    } else if ("string" in parameters) {
      this.fromString(parameters.string);
    } else if ("hexstring" in parameters) {
      this.fromHexString(parameters.hexstring);
    } else {
      if ("length" in parameters && parameters.length > 0) {
        this.length = parameters.length;
        if (parameters.stub) {
          for (var i = 0; i < this._view.length; i++) {
            this._view[i] = parameters.stub;
          }
        }
      } else {
        this.length = 0;
      }
    }
  }
  var _proto = ByteStream.prototype;
  _proto.clear = function clear() {
    this._buffer = new ArrayBuffer(0);
    this._view = new Uint8Array(this._buffer);
  };
  _proto.fromArrayBuffer = function fromArrayBuffer(array) {
    this._buffer = array;
    this._view = new Uint8Array(this._buffer);
  };
  _proto.fromUint8Array = function fromUint8Array(array) {
    this.fromArrayBuffer(new Uint8Array(array).buffer);
  };
  _proto.fromString = function fromString(string) {
    var stringLength = string.length;
    this.length = stringLength;
    for (var i = 0; i < stringLength; i++) this.view[i] = string.charCodeAt(i);
  };
  _proto.toString = function toString(start, length) {
    if (start === void 0) {
      start = 0;
    }
    if (length === void 0) {
      length = this.view.length - start;
    }
    var result = "";
    if (start >= this.view.length || start < 0) {
      start = 0;
    }
    if (length >= this.view.length || length < 0) {
      length = this.view.length - start;
    }
    for (var i = start; i < start + length; i++) result += String.fromCharCode(this.view[i]);
    return result;
  };
  _proto.fromHexString = function fromHexString(hexString) {
    var stringLength = hexString.length;
    this.buffer = new ArrayBuffer(stringLength >> 1);
    this.view = new Uint8Array(this.buffer);
    var hexMap = new Map();
    hexMap.set("0", 0x00);
    hexMap.set("1", 0x01);
    hexMap.set("2", 0x02);
    hexMap.set("3", 0x03);
    hexMap.set("4", 0x04);
    hexMap.set("5", 0x05);
    hexMap.set("6", 0x06);
    hexMap.set("7", 0x07);
    hexMap.set("8", 0x08);
    hexMap.set("9", 0x09);
    hexMap.set("A", 0x0A);
    hexMap.set("a", 0x0A);
    hexMap.set("B", 0x0B);
    hexMap.set("b", 0x0B);
    hexMap.set("C", 0x0C);
    hexMap.set("c", 0x0C);
    hexMap.set("D", 0x0D);
    hexMap.set("d", 0x0D);
    hexMap.set("E", 0x0E);
    hexMap.set("e", 0x0E);
    hexMap.set("F", 0x0F);
    hexMap.set("f", 0x0F);
    var j = 0;
    var temp = 0x00;
    for (var i = 0; i < stringLength; i++) {
      if (!(i % 2)) {
        temp = hexMap.get(hexString.charAt(i)) << 4;
      } else {
        temp |= hexMap.get(hexString.charAt(i));
        this.view[j] = temp;
        j++;
      }
    }
  };
  _proto.toHexString = function toHexString(start, length) {
    if (start === void 0) {
      start = 0;
    }
    if (length === void 0) {
      length = this.view.length - start;
    }
    var result = "";
    if (start >= this.view.length || start < 0) {
      start = 0;
    }
    if (length >= this.view.length || length < 0) {
      length = this.view.length - start;
    }
    for (var i = start; i < start + length; i++) {
      var str = this.view[i].toString(16).toUpperCase();
      result = result + (str.length == 1 ? "0" : "") + str;
    }
    return result;
  };
  _proto.copy = function copy(start, length) {
    if (start === void 0) {
      start = 0;
    }
    if (length === void 0) {
      length = this.length - start;
    }
    if (!start && !this.length) {
      return new ByteStream();
    }
    if (start < 0 || start > this.length - 1) {
      throw new Error(`Wrong start position: ${start}`);
    }
    var stream = new ByteStream({
      buffer: this._buffer.slice(start, start + length)
    });
    return stream;
  };
  _proto.slice = function slice(start, end) {
    if (start === void 0) {
      start = 0;
    }
    if (end === void 0) {
      end = this.length;
    }
    if (!start && !this.length) {
      return new ByteStream();
    }
    if (start < 0 || start > this.length - 1) {
      throw new Error(`Wrong start position: ${start}`);
    }
    var stream = new ByteStream({
      buffer: this._buffer.slice(start, end)
    });
    return stream;
  };
  _proto.realloc = function realloc(size) {
    var buffer = new ArrayBuffer(size);
    var view = new Uint8Array(buffer);
    if (size > this._view.length) view.set(this._view);else {
      view.set(new Uint8Array(this._buffer, 0, size));
    }
    this._buffer = buffer;
    this._view = new Uint8Array(this._buffer);
  };
  _proto.append = function append(stream) {
    var initialSize = this.length;
    var streamViewLength = stream.length;
    var subarrayView = stream._view.subarray();
    this.realloc(initialSize + streamViewLength);
    this._view.set(subarrayView, initialSize);
  };
  _proto.insert = function insert(stream, start, length) {
    if (start === void 0) {
      start = 0;
    }
    if (length === void 0) {
      length = this.length - start;
    }
    if (start > this.length - 1) return false;
    if (length > this.length - start) {
      length = this.length - start;
    }
    if (length > stream.length) {
      length = stream.length;
    }
    if (length == stream.length) this._view.set(stream._view, start);else {
      this._view.set(stream._view.subarray(0, length), start);
    }
    return true;
  };
  _proto.isEqual = function isEqual(stream) {
    if (this.length != stream.length) return false;
    for (var i = 0; i < stream.length; i++) {
      if (this.view[i] != stream.view[i]) return false;
    }
    return true;
  };
  _proto.isEqualView = function isEqualView(view) {
    if (view.length != this.view.length) return false;
    for (var i = 0; i < view.length; i++) {
      if (this.view[i] != view[i]) return false;
    }
    return true;
  };
  _proto.findPattern = function findPattern(pattern, start_, length_, backward_) {
    var _this$prepareFindPara = this.prepareFindParameters(start_, length_, backward_),
      start = _this$prepareFindPara.start,
      length = _this$prepareFindPara.length,
      backward = _this$prepareFindPara.backward;
    var patternLength = pattern.length;
    if (patternLength > length) {
      return -1;
    }
    var patternArray = [];
    for (var i = 0; i < patternLength; i++) patternArray.push(pattern.view[i]);
    for (var _i = 0; _i <= length - patternLength; _i++) {
      var equal = true;
      var equalStart = backward ? start - patternLength - _i : start + _i;
      for (var j = 0; j < patternLength; j++) {
        if (this.view[j + equalStart] != patternArray[j]) {
          equal = false;
          break;
        }
      }
      if (equal) {
        return backward ? start - patternLength - _i : start + patternLength + _i;
      }
    }
    return -1;
  };
  _proto.findFirstIn = function findFirstIn(patterns, start_, length_, backward_) {
    var _this$prepareFindPara2 = this.prepareFindParameters(start_, length_, backward_),
      start = _this$prepareFindPara2.start,
      length = _this$prepareFindPara2.length,
      backward = _this$prepareFindPara2.backward;
    var result = {
      id: -1,
      position: backward ? 0 : start + length,
      length: 0
    };
    for (var i = 0; i < patterns.length; i++) {
      var position = this.findPattern(patterns[i], start, length, backward);
      if (position != -1) {
        var valid = false;
        var patternLength = patterns[i].length;
        if (backward) {
          if (position - patternLength >= result.position - result.length) valid = true;
        } else {
          if (position - patternLength <= result.position - result.length) valid = true;
        }
        if (valid) {
          result.position = position;
          result.id = i;
          result.length = patternLength;
        }
      }
    }
    return result;
  };
  _proto.findAllIn = function findAllIn(patterns, start_, length_) {
    var _this$prepareFindPara3 = this.prepareFindParameters(start_, length_),
      start = _this$prepareFindPara3.start,
      length = _this$prepareFindPara3.length;
    var result = [];
    var patternFound = {
      id: -1,
      position: start
    };
    do {
      var position = patternFound.position;
      patternFound = this.findFirstIn(patterns, patternFound.position, length);
      if (patternFound.id == -1) {
        break;
      }
      length -= patternFound.position - position;
      result.push({
        id: patternFound.id,
        position: patternFound.position
      });
    } while (true);
    return result;
  };
  _proto.findAllPatternIn = function findAllPatternIn(pattern, start_, length_) {
    var _this$prepareFindPara4 = this.prepareFindParameters(start_, length_),
      start = _this$prepareFindPara4.start,
      length = _this$prepareFindPara4.length;
    var result = [];
    var patternLength = pattern.length;
    if (patternLength > length) {
      return -1;
    }
    var patternArray = Array.from(pattern.view);
    for (var i = 0; i <= length - patternLength; i++) {
      var equal = true;
      var equalStart = start + i;
      for (var j = 0; j < patternLength; j++) {
        if (this.view[j + equalStart] != patternArray[j]) {
          equal = false;
          break;
        }
      }
      if (equal) {
        result.push(start + patternLength + i);
        i += patternLength - 1;
      }
    }
    return result;
  };
  _proto.findFirstNotIn = function findFirstNotIn(patterns, start_, length_, backward_) {
    var _this$prepareFindPara5 = this.prepareFindParameters(start_, length_, backward_),
      start = _this$prepareFindPara5.start,
      length = _this$prepareFindPara5.length,
      backward = _this$prepareFindPara5.backward;
    var result = {
      left: {
        id: -1,
        position: start
      },
      right: {
        id: -1,
        position: 0
      },
      value: new ByteStream()
    };
    var currentLength = length;
    while (currentLength > 0) {
      result.right = this.findFirstIn(patterns, backward ? start - length + currentLength : start + length - currentLength, currentLength, backward);
      if (result.right.id == -1) {
        length = currentLength;
        if (backward) {
          start -= length;
        } else {
          start = result.left.position;
        }
        result.value = new ByteStream({
          buffer: this._buffer.slice(start, start + length)
        });
        break;
      }
      if (result.right.position != (backward ? result.left.position - patterns[result.right.id].length : result.left.position + patterns[result.right.id].length)) {
        if (backward) {
          start = result.right.position + patterns[result.right.id].length;
          length = result.left.position - result.right.position - patterns[result.right.id].length;
        } else {
          start = result.left.position;
          length = result.right.position - result.left.position - patterns[result.right.id].length;
        }
        result.value = new ByteStream({
          buffer: this._buffer.slice(start, start + length)
        });
        break;
      }
      result.left = result.right;
      currentLength -= patterns[result.right.id].length;
    }
    if (backward) {
      var temp = result.right;
      result.right = result.left;
      result.left = temp;
    }
    return result;
  };
  _proto.findAllNotIn = function findAllNotIn(patterns, start_, length_) {
    var _this$prepareFindPara6 = this.prepareFindParameters(start_, length_),
      start = _this$prepareFindPara6.start,
      length = _this$prepareFindPara6.length;
    var result = [];
    var patternFound = {
      left: {
        id: -1,
        position: start
      },
      right: {
        id: -1,
        position: start
      },
      value: new ByteStream()
    };
    do {
      var position = patternFound.right.position;
      patternFound = this.findFirstNotIn(patterns, patternFound.right.position, length);
      length -= patternFound.right.position - position;
      result.push({
        left: {
          id: patternFound.left.id,
          position: patternFound.left.position
        },
        right: {
          id: patternFound.right.id,
          position: patternFound.right.position
        },
        value: patternFound.value
      });
    } while (patternFound.right.id != -1);
    return result;
  };
  _proto.findFirstSequence = function findFirstSequence(patterns, start_, length_, backward_) {
    var _this$prepareFindPara7 = this.prepareFindParameters(start_, length_, backward_),
      start = _this$prepareFindPara7.start,
      length = _this$prepareFindPara7.length,
      backward = _this$prepareFindPara7.backward;
    var firstIn = this.skipNotPatterns(patterns, start, length, backward);
    if (firstIn == -1) {
      return {
        position: -1,
        value: new ByteStream()
      };
    }
    var firstNotIn = this.skipPatterns(patterns, firstIn, length - (backward ? start - firstIn : firstIn - start), backward);
    if (backward) {
      start = firstNotIn;
      length = firstIn - firstNotIn;
    } else {
      start = firstIn;
      length = firstNotIn - firstIn;
    }
    var value = new ByteStream({
      buffer: this._buffer.slice(start, start + length)
    });
    return {
      position: firstNotIn,
      value
    };
  };
  _proto.findAllSequences = function findAllSequences(patterns, start_, length_) {
    var _this$prepareFindPara8 = this.prepareFindParameters(start_, length_),
      start = _this$prepareFindPara8.start,
      length = _this$prepareFindPara8.length;
    var result = [];
    var patternFound = {
      position: start,
      value: new ByteStream()
    };
    do {
      var position = patternFound.position;
      patternFound = this.findFirstSequence(patterns, patternFound.position, length);
      if (patternFound.position != -1) {
        length -= patternFound.position - position;
        result.push({
          position: patternFound.position,
          value: patternFound.value
        });
      }
    } while (patternFound.position != -1);
    return result;
  };
  _proto.findPairedPatterns = function findPairedPatterns(leftPattern, rightPattern, start_, length_) {
    var result = [];
    if (leftPattern.isEqual(rightPattern)) return result;
    var _this$prepareFindPara9 = this.prepareFindParameters(start_, length_),
      start = _this$prepareFindPara9.start,
      length = _this$prepareFindPara9.length;
    var currentPositionLeft = 0;
    var leftPatterns = this.findAllPatternIn(leftPattern, start, length);
    if (!Array.isArray(leftPatterns) || leftPatterns.length == 0) {
      return result;
    }
    var rightPatterns = this.findAllPatternIn(rightPattern, start, length);
    if (!Array.isArray(rightPatterns) || rightPatterns.length == 0) {
      return result;
    }
    while (currentPositionLeft < leftPatterns.length) {
      if (rightPatterns.length == 0) {
        break;
      }
      if (leftPatterns[0] == rightPatterns[0]) {
        result.push({
          left: leftPatterns[0],
          right: rightPatterns[0]
        });
        leftPatterns.splice(0, 1);
        rightPatterns.splice(0, 1);
        continue;
      }
      if (leftPatterns[currentPositionLeft] > rightPatterns[0]) {
        break;
      }
      while (leftPatterns[currentPositionLeft] < rightPatterns[0]) {
        currentPositionLeft++;
        if (currentPositionLeft >= leftPatterns.length) {
          break;
        }
      }
      result.push({
        left: leftPatterns[currentPositionLeft - 1],
        right: rightPatterns[0]
      });
      leftPatterns.splice(currentPositionLeft - 1, 1);
      rightPatterns.splice(0, 1);
      currentPositionLeft = 0;
    }
    result.sort((a, b) => a.left - b.left);
    return result;
  };
  _proto.findPairedArrays = function findPairedArrays(inputLeftPatterns, inputRightPatterns, start_, length_) {
    var _this$prepareFindPara10 = this.prepareFindParameters(start_, length_),
      start = _this$prepareFindPara10.start,
      length = _this$prepareFindPara10.length;
    var result = [];
    var currentPositionLeft = 0;
    var leftPatterns = this.findAllIn(inputLeftPatterns, start, length);
    if (leftPatterns.length == 0) return result;
    var rightPatterns = this.findAllIn(inputRightPatterns, start, length);
    if (rightPatterns.length == 0) return result;
    while (currentPositionLeft < leftPatterns.length) {
      if (rightPatterns.length == 0) {
        break;
      }
      if (leftPatterns[0].position == rightPatterns[0].position) {
        result.push({
          left: leftPatterns[0],
          right: rightPatterns[0]
        });
        leftPatterns.splice(0, 1);
        rightPatterns.splice(0, 1);
        continue;
      }
      if (leftPatterns[currentPositionLeft].position > rightPatterns[0].position) {
        break;
      }
      while (leftPatterns[currentPositionLeft].position < rightPatterns[0].position) {
        currentPositionLeft++;
        if (currentPositionLeft >= leftPatterns.length) {
          break;
        }
      }
      result.push({
        left: leftPatterns[currentPositionLeft - 1],
        right: rightPatterns[0]
      });
      leftPatterns.splice(currentPositionLeft - 1, 1);
      rightPatterns.splice(0, 1);
      currentPositionLeft = 0;
    }
    result.sort((a, b) => a.left.position - b.left.position);
    return result;
  };
  _proto.replacePattern = function replacePattern(searchPattern, _replacePattern, start_, length_, findAllResult) {
    var _output$searchPattern;
    if (findAllResult === void 0) {
      findAllResult = null;
    }
    var result = [];
    var i;
    var output = {
      status: -1,
      searchPatternPositions: [],
      replacePatternPositions: []
    };
    var _this$prepareFindPara11 = this.prepareFindParameters(start_, length_),
      start = _this$prepareFindPara11.start,
      length = _this$prepareFindPara11.length;
    if (findAllResult == null) {
      result = this.findAllIn([searchPattern], start, length);
      if (result.length == 0) {
        return output;
      }
    } else {
      result = findAllResult;
    }
    (_output$searchPattern = output.searchPatternPositions).push.apply(_output$searchPattern, Array.from(result, element => element.position));
    var patternDifference = searchPattern.length - _replacePattern.length;
    var changedBuffer = new ArrayBuffer(this.view.length - result.length * patternDifference);
    var changedView = new Uint8Array(changedBuffer);
    changedView.set(new Uint8Array(this.buffer, 0, start));
    for (i = 0; i < result.length; i++) {
      var currentPosition = i == 0 ? start : result[i - 1].position;
      changedView.set(new Uint8Array(this.buffer, currentPosition, result[i].position - searchPattern.length - currentPosition), currentPosition - i * patternDifference);
      changedView.set(_replacePattern.view, result[i].position - searchPattern.length - i * patternDifference);
      output.replacePatternPositions.push(result[i].position - searchPattern.length - i * patternDifference);
    }
    i--;
    changedView.set(new Uint8Array(this.buffer, result[i].position, this.length - result[i].position), result[i].position - searchPattern.length + _replacePattern.length - i * patternDifference);
    this.buffer = changedBuffer;
    this.view = new Uint8Array(this.buffer);
    output.status = 1;
    return output;
  };
  _proto.skipPatterns = function skipPatterns(patterns, start_, length_, backward_) {
    var _this$prepareFindPara12 = this.prepareFindParameters(start_, length_, backward_),
      start = _this$prepareFindPara12.start,
      length = _this$prepareFindPara12.length,
      backward = _this$prepareFindPara12.backward;
    var result = start;
    for (var k = 0; k < patterns.length; k++) {
      var patternLength = patterns[k].length;
      var equalStart = backward ? result - patternLength : result;
      var equal = true;
      for (var j = 0; j < patternLength; j++) {
        if (this.view[j + equalStart] != patterns[k].view[j]) {
          equal = false;
          break;
        }
      }
      if (equal) {
        k = -1;
        if (backward) {
          result -= patternLength;
          if (result <= 0) return result;
        } else {
          result += patternLength;
          if (result >= start + length) return result;
        }
      }
    }
    return result;
  };
  _proto.skipNotPatterns = function skipNotPatterns(patterns, start_, length_, backward_) {
    var _this$prepareFindPara13 = this.prepareFindParameters(start_, length_, backward_),
      start = _this$prepareFindPara13.start,
      length = _this$prepareFindPara13.length,
      backward = _this$prepareFindPara13.backward;
    var result = -1;
    for (var i = 0; i < length; i++) {
      for (var k = 0; k < patterns.length; k++) {
        var patternLength = patterns[k].length;
        var equalStart = backward ? start - i - patternLength : start + i;
        var equal = true;
        for (var j = 0; j < patternLength; j++) {
          if (this.view[j + equalStart] != patterns[k].view[j]) {
            equal = false;
            break;
          }
        }
        if (equal) {
          result = backward ? start - i : start + i;
          break;
        }
      }
      if (result != -1) {
        break;
      }
    }
    return result;
  };
  _proto.prepareFindParameters = function prepareFindParameters(start, length, backward) {
    if (start === void 0) {
      start = null;
    }
    if (length === void 0) {
      length = null;
    }
    if (backward === void 0) {
      backward = false;
    }
    if (start === null) {
      start = backward ? this.length : 0;
    }
    if (start > this.length) {
      start = this.length;
    }
    if (backward) {
      if (length === null) {
        length = start;
      }
      if (length > start) {
        length = start;
      }
    } else {
      if (length === null) {
        length = this.length - start;
      }
      if (length > this.length - start) {
        length = this.length - start;
      }
    }
    return {
      start,
      length,
      backward
    };
  };
  _createClass(ByteStream, [{
    key: "buffer",
    get: function () {
      return this._buffer;
    },
    set: function (value) {
      this._buffer = value;
      this._view = new Uint8Array(this._buffer);
    }
  }, {
    key: "view",
    get: function () {
      return this._view;
    },
    set: function (value) {
      this._buffer = new ArrayBuffer(value.length);
      this._view = new Uint8Array(this._buffer);
      this._view.set(value);
    }
  }, {
    key: "length",
    get: function () {
      return this.view.byteLength;
    },
    set: function (value) {
      this._buffer = new ArrayBuffer(value);
      this._view = new Uint8Array(this._buffer);
    }
  }]);
  return ByteStream;
}();

var pow2_24 = 16777216;
var SeqStream = /*#__PURE__*/function () {
  function SeqStream(parameters) {
    if (parameters === void 0) {
      parameters = {};
    }
    this._stream = new ByteStream();
    this._length = 0;
    this._start = 0;
    this.backward = false;
    this.appendBlock = 0;
    this.prevLength = 0;
    this.prevStart = 0;
    if ("view" in parameters) {
      this.stream = new ByteStream({
        view: parameters.view
      });
    } else if ("buffer" in parameters) {
      this.stream = new ByteStream({
        buffer: parameters.buffer
      });
    } else if ("string" in parameters) {
      this.stream = new ByteStream({
        string: parameters.string
      });
    } else if ("hexstring" in parameters) {
      this.stream = new ByteStream({
        hexstring: parameters.hexstring
      });
    } else if ("stream" in parameters) {
      this.stream = parameters.stream.slice();
    } else {
      this.stream = new ByteStream();
    }
    if ("backward" in parameters && parameters.backward) {
      this.backward = parameters.backward;
      this._start = this.stream.length;
    }
    if ("length" in parameters && parameters.length > 0) {
      this._length = parameters.length;
    }
    if ("start" in parameters && parameters.start && parameters.start > 0) {
      this._start = parameters.start;
    }
    if ("appendBlock" in parameters && parameters.appendBlock && parameters.appendBlock > 0) {
      this.appendBlock = parameters.appendBlock;
    }
  }
  var _proto = SeqStream.prototype;
  _proto.resetPosition = function resetPosition() {
    this._start = this.prevStart;
    this._length = this.prevLength;
  };
  _proto.findPattern = function findPattern(pattern, gap) {
    if (gap === void 0) {
      gap = null;
    }
    if (gap == null || gap > this.length) {
      gap = this.length;
    }
    var result = this.stream.findPattern(pattern, this.start, this.length, this.backward);
    if (result == -1) return result;
    if (this.backward) {
      if (result < this.start - pattern.length - gap) {
        return -1;
      }
    } else {
      if (result > this.start + pattern.length + gap) {
        return -1;
      }
    }
    this.start = result;
    return result;
  };
  _proto.findFirstIn = function findFirstIn(patterns, gap) {
    if (gap === void 0) {
      gap = null;
    }
    if (gap == null || gap > this.length) {
      gap = this.length;
    }
    var result = this.stream.findFirstIn(patterns, this.start, this.length, this.backward);
    if (result.id == -1) return result;
    if (this.backward) {
      if (result.position < this.start - patterns[result.id].length - gap) {
        return {
          id: -1,
          position: this.backward ? 0 : this.start + this.length
        };
      }
    } else {
      if (result.position > this.start + patterns[result.id].length + gap) {
        return {
          id: -1,
          position: this.backward ? 0 : this.start + this.length
        };
      }
    }
    this.start = result.position;
    return result;
  };
  _proto.findAllIn = function findAllIn(patterns) {
    var start = this.backward ? this.start - this.length : this.start;
    return this.stream.findAllIn(patterns, start, this.length);
  };
  _proto.findFirstNotIn = function findFirstNotIn(patterns, gap) {
    if (gap === void 0) {
      gap = null;
    }
    if (gap == null || gap > this._length) {
      gap = this._length;
    }
    var result = this._stream.findFirstNotIn(patterns, this._start, this._length, this.backward);
    if (result.left.id == -1 && result.right.id == -1) {
      return result;
    }
    if (this.backward) {
      if (result.right.id != -1) {
        if (result.right.position < this._start - patterns[result.right.id].length - gap) {
          return {
            left: {
              id: -1,
              position: this._start
            },
            right: {
              id: -1,
              position: 0
            },
            value: new ByteStream()
          };
        }
      }
    } else {
      if (result.left.id != -1) {
        if (result.left.position > this._start + patterns[result.left.id].length + gap) {
          return {
            left: {
              id: -1,
              position: this._start
            },
            right: {
              id: -1,
              position: 0
            },
            value: new ByteStream()
          };
        }
      }
    }
    if (this.backward) {
      if (result.left.id == -1) {
        this.start = 0;
      } else {
        this.start = result.left.position;
      }
    } else {
      if (result.right.id == -1) {
        this.start = this._start + this._length;
      } else {
        this.start = result.right.position;
      }
    }
    return result;
  };
  _proto.findAllNotIn = function findAllNotIn(patterns) {
    var start = this.backward ? this._start - this._length : this._start;
    return this._stream.findAllNotIn(patterns, start, this._length);
  };
  _proto.findFirstSequence = function findFirstSequence(patterns, length, gap) {
    if (length === void 0) {
      length = null;
    }
    if (gap === void 0) {
      gap = null;
    }
    if (length == null || length > this._length) {
      length = this._length;
    }
    if (gap == null || gap > length) {
      gap = length;
    }
    var result = this._stream.findFirstSequence(patterns, this._start, length, this.backward);
    if (result.value.length == 0) {
      return result;
    }
    if (this.backward) {
      if (result.position < this._start - result.value.length - gap) {
        return {
          position: -1,
          value: new ByteStream()
        };
      }
    } else {
      if (result.position > this._start + result.value.length + gap) {
        return {
          position: -1,
          value: new ByteStream()
        };
      }
    }
    this.start = result.position;
    return result;
  };
  _proto.findAllSequences = function findAllSequences(patterns) {
    var start = this.backward ? this.start - this.length : this.start;
    return this.stream.findAllSequences(patterns, start, this.length);
  };
  _proto.findPairedPatterns = function findPairedPatterns(leftPattern, rightPattern, gap) {
    if (gap === void 0) {
      gap = null;
    }
    if (gap == null || gap > this.length) {
      gap = this.length;
    }
    var start = this.backward ? this.start - this.length : this.start;
    var result = this.stream.findPairedPatterns(leftPattern, rightPattern, start, this.length);
    if (result.length) {
      if (this.backward) {
        if (result[0].right < this.start - rightPattern.length - gap) {
          return [];
        }
      } else {
        if (result[0].left > this.start + leftPattern.length + gap) {
          return [];
        }
      }
    }
    return result;
  };
  _proto.findPairedArrays = function findPairedArrays(leftPatterns, rightPatterns, gap) {
    if (gap === void 0) {
      gap = null;
    }
    if (gap == null || gap > this.length) {
      gap = this.length;
    }
    var start = this.backward ? this.start - this.length : this.start;
    var result = this.stream.findPairedArrays(leftPatterns, rightPatterns, start, this.length);
    if (result.length) {
      if (this.backward) {
        if (result[0].right.position < this.start - rightPatterns[result[0].right.id].length - gap) {
          return [];
        }
      } else {
        if (result[0].left.position > this.start + leftPatterns[result[0].left.id].length + gap) {
          return [];
        }
      }
    }
    return result;
  };
  _proto.replacePattern = function replacePattern(searchPattern, _replacePattern) {
    var start = this.backward ? this.start - this.length : this.start;
    return this.stream.replacePattern(searchPattern, _replacePattern, start, this.length);
  };
  _proto.skipPatterns = function skipPatterns(patterns) {
    var result = this.stream.skipPatterns(patterns, this.start, this.length, this.backward);
    this.start = result;
    return result;
  };
  _proto.skipNotPatterns = function skipNotPatterns(patterns) {
    var result = this.stream.skipNotPatterns(patterns, this.start, this.length, this.backward);
    if (result == -1) return -1;
    this.start = result;
    return result;
  };
  _proto.append = function append(stream) {
    this.beforeAppend(stream.length);
    this._stream.view.set(stream.view, this._start);
    this._length += stream.length * 2;
    this.start = this._start + stream.length;
    this.prevLength -= stream.length * 2;
  };
  _proto.appendView = function appendView(view) {
    this.beforeAppend(view.length);
    this._stream.view.set(view, this._start);
    this._length += view.length * 2;
    this.start = this._start + view.length;
    this.prevLength -= view.length * 2;
  };
  _proto.appendChar = function appendChar(char) {
    this.beforeAppend(1);
    this._stream.view[this._start] = char;
    this._length += 2;
    this.start = this._start + 1;
    this.prevLength -= 2;
  };
  _proto.appendUint16 = function appendUint16(number) {
    this.beforeAppend(2);
    var value = new Uint16Array([number]);
    var view = new Uint8Array(value.buffer);
    this.stream.view[this._start] = view[1];
    this._stream.view[this._start + 1] = view[0];
    this._length += 4;
    this.start = this._start + 2;
    this.prevLength -= 4;
  };
  _proto.appendUint24 = function appendUint24(number) {
    this.beforeAppend(3);
    var value = new Uint32Array([number]);
    var view = new Uint8Array(value.buffer);
    this._stream.view[this._start] = view[2];
    this._stream.view[this._start + 1] = view[1];
    this._stream.view[this._start + 2] = view[0];
    this._length += 6;
    this.start = this._start + 3;
    this.prevLength -= 6;
  };
  _proto.appendUint32 = function appendUint32(number) {
    this.beforeAppend(4);
    var value = new Uint32Array([number]);
    var view = new Uint8Array(value.buffer);
    this._stream.view[this._start] = view[3];
    this._stream.view[this._start + 1] = view[2];
    this._stream.view[this._start + 2] = view[1];
    this._stream.view[this._start + 3] = view[0];
    this._length += 8;
    this.start = this._start + 4;
    this.prevLength -= 8;
  };
  _proto.appendInt16 = function appendInt16(number) {
    this.beforeAppend(2);
    var value = new Int16Array([number]);
    var view = new Uint8Array(value.buffer);
    this._stream.view[this._start] = view[1];
    this._stream.view[this._start + 1] = view[0];
    this._length += 4;
    this.start = this._start + 2;
    this.prevLength -= 4;
  };
  _proto.appendInt32 = function appendInt32(number) {
    this.beforeAppend(4);
    var value = new Int32Array([number]);
    var view = new Uint8Array(value.buffer);
    this._stream.view[this._start] = view[3];
    this._stream.view[this._start + 1] = view[2];
    this._stream.view[this._start + 2] = view[1];
    this._stream.view[this._start + 3] = view[0];
    this._length += 8;
    this.start = this._start + 4;
    this.prevLength -= 8;
  };
  _proto.getBlock = function getBlock(size, changeLength) {
    if (changeLength === void 0) {
      changeLength = true;
    }
    if (this._length <= 0) {
      return new Uint8Array(0);
    }
    if (this._length < size) {
      size = this._length;
    }
    var result;
    if (this.backward) {
      var view = this._stream.view.subarray(this._length - size, this._length);
      result = new Uint8Array(size);
      for (var i = 0; i < size; i++) {
        result[size - 1 - i] = view[i];
      }
    } else {
      result = this._stream.view.subarray(this._start, this._start + size);
    }
    if (changeLength) {
      this.start += this.backward ? -1 * size : size;
    }
    return result;
  };
  _proto.getUint16 = function getUint16(changeLength) {
    if (changeLength === void 0) {
      changeLength = true;
    }
    var block = this.getBlock(2, changeLength);
    if (block.length < 2) return 0;
    return block[0] << 8 | block[1];
  };
  _proto.getInt16 = function getInt16(changeLength) {
    if (changeLength === void 0) {
      changeLength = true;
    }
    var num = this.getUint16(changeLength);
    var negative = 0x8000;
    if (num & negative) {
      return -(negative - (num ^ negative));
    }
    return num;
  };
  _proto.getUint24 = function getUint24(changeLength) {
    if (changeLength === void 0) {
      changeLength = true;
    }
    var block = this.getBlock(4, changeLength);
    if (block.length < 3) return 0;
    return block[0] << 16 | block[1] << 8 | block[2];
  };
  _proto.getUint32 = function getUint32(changeLength) {
    if (changeLength === void 0) {
      changeLength = true;
    }
    var block = this.getBlock(4, changeLength);
    if (block.length < 4) return 0;
    return block[0] * pow2_24 + (block[1] << 16) + (block[2] << 8) + block[3];
  };
  _proto.getInt32 = function getInt32(changeLength) {
    if (changeLength === void 0) {
      changeLength = true;
    }
    var num = this.getUint32(changeLength);
    var negative = 0x80000000;
    if (num & negative) {
      return -(negative - (num ^ negative));
    }
    return num;
  };
  _proto.beforeAppend = function beforeAppend(size) {
    if (this._start + size > this._stream.length) {
      if (size > this.appendBlock) {
        this.appendBlock = size + SeqStream.APPEND_BLOCK;
      }
      this._stream.realloc(this._stream.length + this.appendBlock);
    }
  };
  _createClass(SeqStream, [{
    key: "stream",
    get: function () {
      return this._stream;
    },
    set: function (value) {
      this._stream = value;
      this.prevLength = this._length;
      this._length = value.length;
      this.prevStart = this._start;
      this._start = 0;
    }
  }, {
    key: "length",
    get: function () {
      if (this.appendBlock) {
        return this.start;
      }
      return this._length;
    },
    set: function (value) {
      this.prevLength = this._length;
      this._length = value;
    }
  }, {
    key: "start",
    get: function () {
      return this._start;
    },
    set: function (value) {
      if (value > this.stream.length) return;
      this.prevStart = this._start;
      this.prevLength = this._length;
      this._length -= this.backward ? this._start - value : value - this._start;
      this._start = value;
    }
  }, {
    key: "buffer",
    get: function () {
      return this._stream.buffer.slice(0, this._length);
    }
  }]);
  return SeqStream;
}();
SeqStream.APPEND_BLOCK = 1000;

var makePKCS12B2Key=_async((cryptoEngine,hashAlgorithm,keyLength,password,salt,iterationCount)=>{var u;var v;var result=[];switch(hashAlgorithm.toUpperCase()){case"SHA-1":u=20;v=64;break;case"SHA-256":u=32;v=64;break;case"SHA-384":u=48;v=128;break;case"SHA-512":u=64;v=128;break;default:throw new Error("Unsupported hashing algorithm");}var passwordViewInitial=new Uint8Array(password);var passwordTransformed=new ArrayBuffer(password.byteLength*2+2);var passwordTransformedView=new Uint8Array(passwordTransformed);for(var _i72=0;_i72<passwordViewInitial.length;_i72++){passwordTransformedView[_i72*2]=0x00;passwordTransformedView[_i72*2+1]=passwordViewInitial[_i72];}passwordTransformedView[passwordTransformedView.length-2]=0x00;passwordTransformedView[passwordTransformedView.length-1]=0x00;password=passwordTransformed.slice(0);var D=new ArrayBuffer(v);var dView=new Uint8Array(D);for(var _i73=0;_i73<D.byteLength;_i73++)dView[_i73]=3;var saltLength=salt.byteLength;var sLen=v*Math.ceil(saltLength/v);var S=new ArrayBuffer(sLen);var sView=new Uint8Array(S);var saltView=new Uint8Array(salt);for(var _i74=0;_i74<sLen;_i74++)sView[_i74]=saltView[_i74%saltLength];var passwordLength=password.byteLength;var pLen=v*Math.ceil(passwordLength/v);var P=new ArrayBuffer(pLen);var pView=new Uint8Array(P);var passwordView=new Uint8Array(password);for(var _i75=0;_i75<pLen;_i75++)pView[_i75]=passwordView[_i75%passwordLength];var sPlusPLength=S.byteLength+P.byteLength;var I=new ArrayBuffer(sPlusPLength);var iView=new Uint8Array(I);iView.set(sView);iView.set(pView,sView.length);var c=Math.ceil((keyLength>>3)/u);var internalSequence=Promise.resolve(I);for(var _i76=0;_i76<=c;_i76++){internalSequence=internalSequence.then(_I=>{var dAndI=new ArrayBuffer(D.byteLength+_I.byteLength);var dAndIView=new Uint8Array(dAndI);dAndIView.set(dView);dAndIView.set(iView,dView.length);return dAndI;});for(var _j16=0;_j16<iterationCount;_j16++)internalSequence=internalSequence.then(roundBuffer=>cryptoEngine.digest({name:hashAlgorithm},new Uint8Array(roundBuffer)));internalSequence=internalSequence.then(roundBuffer=>{var B=new ArrayBuffer(v);var bView=new Uint8Array(B);for(var _j17=0;_j17<B.byteLength;_j17++)bView[_j17]=roundBuffer[_j17%roundBuffer.byteLength];var k=Math.ceil(saltLength/v)+Math.ceil(passwordLength/v);var iRound=[];var sliceStart=0;var sliceLength=v;for(var _j18=0;_j18<k;_j18++){var chunk=Array.from(new Uint8Array(I.slice(sliceStart,sliceStart+sliceLength)));sliceStart+=v;if(sliceStart+v>I.byteLength)sliceLength=I.byteLength-sliceStart;var x=0x1ff;for(var l=B.byteLength-1;l>=0;l--){x>>=8;x+=bView[l]+chunk[l];chunk[l]=x&0xff;}iRound.push.apply(iRound,chunk);}I=new ArrayBuffer(iRound.length);iView=new Uint8Array(I);iView.set(iRound);result.push.apply(result,new Uint8Array(roundBuffer));return I;});}internalSequence=internalSequence.then(()=>{var resultBuffer=new ArrayBuffer(keyLength>>3);var resultView=new Uint8Array(resultBuffer);resultView.set(new Uint8Array(result).slice(0,keyLength>>3));return resultBuffer;});return internalSequence;});var EMPTY_BUFFER=new ArrayBuffer(0);var EMPTY_STRING="";var ArgumentError=/*#__PURE__*/function(_TypeError){_inheritsLoose(ArgumentError,_TypeError);function ArgumentError(){var _this;_this=_TypeError.apply(this,arguments)||this;_this.name=ArgumentError.NAME;return _this;}ArgumentError.isType=function isType(value,type){if(typeof type==="string"){if(type==="Array"&&Array.isArray(value)){return true;}else if(type==="ArrayBuffer"&&value instanceof ArrayBuffer){return true;}else if(type==="ArrayBufferView"&&ArrayBuffer.isView(value)){return true;}else if(typeof value===type){return true;}}else if(value instanceof type){return true;}return false;};ArgumentError.assert=function assert(value,name){for(var _len=arguments.length,types=new Array(_len>2?_len-2:0),_key=2;_key<_len;_key++){types[_key-2]=arguments[_key];}for(var _i2=0;_i2<types.length;_i2++){var type=types[_i2];if(this.isType(value,type)){return;}}var typeNames=types.map(o=>o instanceof Function&&"name"in o?o.name:`${o}`);throw new ArgumentError(`Parameter '${name}' is not of type ${typeNames.length>1?`(${typeNames.join(" or ")})`:typeNames[0]}`);};return ArgumentError;}(/*#__PURE__*/_wrapNativeSuper(TypeError));ArgumentError.NAME="ArgumentError";var ParameterError=/*#__PURE__*/function(_TypeError2){_inheritsLoose(ParameterError,_TypeError2);function ParameterError(field,target,message){var _this2;if(target===void 0){target=null;}_this2=_TypeError2.call(this)||this;_this2.name=ParameterError.NAME;_this2.field=field;if(target){_this2.target=target;}if(message){_this2.message=message;}else {_this2.message=`Absent mandatory parameter '${field}' ${target?` in '${target}'`:EMPTY_STRING}`;}return _this2;}ParameterError.assert=function assert(){var target=null;var params;var fields;for(var _len2=arguments.length,args=new Array(_len2),_key2=0;_key2<_len2;_key2++){args[_key2]=arguments[_key2];}if(typeof args[0]==="string"){target=args[0];params=args[1];fields=args.slice(2);}else {params=args[0];fields=args.slice(1);}ArgumentError.assert(params,"parameters","object");for(var _i4=0,_fields2=fields;_i4<_fields2.length;_i4++){var field=_fields2[_i4];var value=params[field];if(value===undefined||value===null){throw new ParameterError(field,target);}}};ParameterError.assertEmpty=function assertEmpty(value,name,target){if(value===undefined||value===null){throw new ParameterError(name,target);}};return ParameterError;}(/*#__PURE__*/_wrapNativeSuper(TypeError));ParameterError.NAME="ParameterError";var AsnError=/*#__PURE__*/function(_Error){_inheritsLoose(AsnError,_Error);AsnError.assertSchema=function assertSchema(asn1,target){if(!asn1.verified){throw new Error(`Object's schema was not verified against input data for ${target}`);}};AsnError.assert=function assert(asn,target){if(asn.offset===-1){throw new AsnError(`Error during parsing of ASN.1 data. Data is not correct for '${target}'.`);}};function AsnError(message){var _this3;_this3=_Error.call(this,message)||this;_this3.name="AsnError";return _this3;}return AsnError;}(/*#__PURE__*/_wrapNativeSuper(Error));var PkiObject=/*#__PURE__*/function(){function PkiObject(){}PkiObject.blockName=function blockName(){return this.CLASS_NAME;};PkiObject.fromBER=function fromBER$1(raw){var asn1=fromBER(raw);AsnError.assert(asn1,this.name);try{return new this({schema:asn1.result});}catch(e){throw new AsnError(`Cannot create '${this.CLASS_NAME}' from ASN.1 object`);}};PkiObject.defaultValues=function defaultValues(memberName){throw new Error(`Invalid member name for ${this.CLASS_NAME} class: ${memberName}`);};PkiObject.schema=function schema(parameters){throw new Error(`Method '${this.CLASS_NAME}.schema' should be overridden`);};var _proto=PkiObject.prototype;_proto.toString=function toString(encoding){if(encoding===void 0){encoding="hex";}var schema;try{schema=this.toSchema();}catch(_unused){schema=this.toSchema(true);}return Convert.ToString(schema.toBER(),encoding);};_createClass(PkiObject,[{key:"className",get:function(){return this.constructor.CLASS_NAME;}}]);return PkiObject;}();PkiObject.CLASS_NAME="PkiObject";function stringPrep(inputString){var isSpace=false;var cutResult=EMPTY_STRING;var result=inputString.trim();for(var i=0;i<result.length;i++){if(result.charCodeAt(i)===32){if(isSpace===false)isSpace=true;}else {if(isSpace){cutResult+=" ";isSpace=false;}cutResult+=result[i];}}return cutResult.toLowerCase();}var TYPE$5="type";var VALUE$6="value";var AttributeTypeAndValue=/*#__PURE__*/function(_PkiObject){_inheritsLoose(AttributeTypeAndValue,_PkiObject);function AttributeTypeAndValue(parameters){var _this4;if(parameters===void 0){parameters={};}_this4=_PkiObject.call(this)||this;_this4.type=getParametersValue(parameters,TYPE$5,AttributeTypeAndValue.defaultValues(TYPE$5));_this4.value=getParametersValue(parameters,VALUE$6,AttributeTypeAndValue.defaultValues(VALUE$6));if(parameters.schema){_this4.fromSchema(parameters.schema);}return _this4;}AttributeTypeAndValue.defaultValues=function defaultValues(memberName){switch(memberName){case TYPE$5:return EMPTY_STRING;case VALUE$6:return {};default:return _PkiObject.defaultValues.call(this,memberName);}};AttributeTypeAndValue.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new ObjectIdentifier({name:names.type||EMPTY_STRING}),new Any({name:names.value||EMPTY_STRING})]});};var _proto2=AttributeTypeAndValue.prototype;_proto2.fromSchema=function fromSchema(schema){clearProps(schema,[TYPE$5,"typeValue"]);var asn1=compareSchema(schema,schema,AttributeTypeAndValue.schema({names:{type:TYPE$5,value:"typeValue"}}));AsnError.assertSchema(asn1,this.className);this.type=asn1.result.type.valueBlock.toString();this.value=asn1.result.typeValue;};_proto2.toSchema=function toSchema(){return new Sequence({value:[new ObjectIdentifier({value:this.type}),this.value]});};_proto2.toJSON=function toJSON(){var _object={type:this.type};if(Object.keys(this.value).length!==0){_object.value=this.value.toJSON();}else {_object.value=this.value;}return _object;};_proto2.isEqual=function isEqual(compareTo){var stringBlockNames=[Utf8String.blockName(),BmpString.blockName(),UniversalString.blockName(),NumericString.blockName(),PrintableString.blockName(),TeletexString.blockName(),VideotexString.blockName(),IA5String.blockName(),GraphicString.blockName(),VisibleString.blockName(),GeneralString.blockName(),CharacterString.blockName()];if(compareTo instanceof ArrayBuffer){return BufferSourceConverter.isEqual(this.value.valueBeforeDecodeView,compareTo);}if(compareTo.constructor.blockName()===AttributeTypeAndValue.blockName()){if(this.type!==compareTo.type)return false;var isStringPair=[false,false];var thisName=this.value.constructor.blockName();for(var _i6=0;_i6<stringBlockNames.length;_i6++){var name=stringBlockNames[_i6];if(thisName===name){isStringPair[0]=true;}if(compareTo.value.constructor.blockName()===name){isStringPair[1]=true;}}if(isStringPair[0]!==isStringPair[1]){return false;}var isString=isStringPair[0]&&isStringPair[1];if(isString){var value1=stringPrep(this.value.valueBlock.value);var value2=stringPrep(compareTo.value.valueBlock.value);if(value1.localeCompare(value2)!==0)return false;}else {if(!BufferSourceConverter.isEqual(this.value.valueBeforeDecodeView,compareTo.value.valueBeforeDecodeView))return false;}return true;}return false;};return AttributeTypeAndValue;}(PkiObject);AttributeTypeAndValue.CLASS_NAME="AttributeTypeAndValue";var TYPE_AND_VALUES="typesAndValues";var VALUE_BEFORE_DECODE="valueBeforeDecode";var RDN="RDN";var RelativeDistinguishedNames=/*#__PURE__*/function(_PkiObject2){_inheritsLoose(RelativeDistinguishedNames,_PkiObject2);function RelativeDistinguishedNames(parameters){var _this5;if(parameters===void 0){parameters={};}_this5=_PkiObject2.call(this)||this;_this5.typesAndValues=getParametersValue(parameters,TYPE_AND_VALUES,RelativeDistinguishedNames.defaultValues(TYPE_AND_VALUES));_this5.valueBeforeDecode=getParametersValue(parameters,VALUE_BEFORE_DECODE,RelativeDistinguishedNames.defaultValues(VALUE_BEFORE_DECODE));if(parameters.schema){_this5.fromSchema(parameters.schema);}return _this5;}RelativeDistinguishedNames.defaultValues=function defaultValues(memberName){switch(memberName){case TYPE_AND_VALUES:return [];case VALUE_BEFORE_DECODE:return EMPTY_BUFFER;default:return _PkiObject2.defaultValues.call(this,memberName);}};RelativeDistinguishedNames.compareWithDefault=function compareWithDefault(memberName,memberValue){switch(memberName){case TYPE_AND_VALUES:return memberValue.length===0;case VALUE_BEFORE_DECODE:return memberValue.byteLength===0;default:return _PkiObject2.defaultValues.call(this,memberName);}};RelativeDistinguishedNames.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Repeated({name:names.repeatedSequence||EMPTY_STRING,value:new Set({value:[new Repeated({name:names.repeatedSet||EMPTY_STRING,value:AttributeTypeAndValue.schema(names.typeAndValue||{})})]})})]});};var _proto3=RelativeDistinguishedNames.prototype;_proto3.fromSchema=function fromSchema(schema){clearProps(schema,[RDN,TYPE_AND_VALUES]);var asn1=compareSchema(schema,schema,RelativeDistinguishedNames.schema({names:{blockName:RDN,repeatedSet:TYPE_AND_VALUES}}));AsnError.assertSchema(asn1,this.className);if(TYPE_AND_VALUES in asn1.result){this.typesAndValues=Array.from(asn1.result.typesAndValues,element=>new AttributeTypeAndValue({schema:element}));}this.valueBeforeDecode=asn1.result.RDN.valueBeforeDecodeView.slice().buffer;};_proto3.toSchema=function toSchema(){if(this.valueBeforeDecode.byteLength===0){return new Sequence({value:[new Set({value:Array.from(this.typesAndValues,o=>o.toSchema())})]});}var asn1=fromBER(this.valueBeforeDecode);AsnError.assert(asn1,"RelativeDistinguishedNames");if(!(asn1.result instanceof Sequence)){throw new Error("ASN.1 result should be SEQUENCE");}return asn1.result;};_proto3.toJSON=function toJSON(){return {typesAndValues:Array.from(this.typesAndValues,o=>o.toJSON())};};_proto3.isEqual=function isEqual(compareTo){if(compareTo instanceof RelativeDistinguishedNames){if(this.typesAndValues.length!==compareTo.typesAndValues.length)return false;for(var _i8=0,_this$typesAndValues$2=this.typesAndValues.entries();_i8<_this$typesAndValues$2.length;_i8++){var _ref=_this$typesAndValues$2[_i8];var index=_ref[0];var typeAndValue=_ref[1];if(typeAndValue.isEqual(compareTo.typesAndValues[index])===false)return false;}return true;}if(compareTo instanceof ArrayBuffer){return isEqualBuffer(this.valueBeforeDecode,compareTo);}return false;};return RelativeDistinguishedNames;}(PkiObject);RelativeDistinguishedNames.CLASS_NAME="RelativeDistinguishedNames";var TYPE$4="type";var VALUE$5="value";function builtInStandardAttributes(parameters,optional){if(parameters===void 0){parameters={};}if(optional===void 0){optional=false;}var names=getParametersValue(parameters,"names",{});return new Sequence({optional,value:[new Constructed({optional:true,idBlock:{tagClass:2,tagNumber:1},name:names.country_name||EMPTY_STRING,value:[new Choice({value:[new NumericString(),new PrintableString()]})]}),new Constructed({optional:true,idBlock:{tagClass:2,tagNumber:2},name:names.administration_domain_name||EMPTY_STRING,value:[new Choice({value:[new NumericString(),new PrintableString()]})]}),new Primitive({optional:true,idBlock:{tagClass:3,tagNumber:0},name:names.network_address||EMPTY_STRING,isHexOnly:true}),new Primitive({optional:true,idBlock:{tagClass:3,tagNumber:1},name:names.terminal_identifier||EMPTY_STRING,isHexOnly:true}),new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:2},name:names.private_domain_name||EMPTY_STRING,value:[new Choice({value:[new NumericString(),new PrintableString()]})]}),new Primitive({optional:true,idBlock:{tagClass:3,tagNumber:3},name:names.organization_name||EMPTY_STRING,isHexOnly:true}),new Primitive({optional:true,name:names.numeric_user_identifier||EMPTY_STRING,idBlock:{tagClass:3,tagNumber:4},isHexOnly:true}),new Constructed({optional:true,name:names.personal_name||EMPTY_STRING,idBlock:{tagClass:3,tagNumber:5},value:[new Primitive({idBlock:{tagClass:3,tagNumber:0},isHexOnly:true}),new Primitive({optional:true,idBlock:{tagClass:3,tagNumber:1},isHexOnly:true}),new Primitive({optional:true,idBlock:{tagClass:3,tagNumber:2},isHexOnly:true}),new Primitive({optional:true,idBlock:{tagClass:3,tagNumber:3},isHexOnly:true})]}),new Constructed({optional:true,name:names.organizational_unit_names||EMPTY_STRING,idBlock:{tagClass:3,tagNumber:6},value:[new Repeated({value:new PrintableString()})]})]});}function builtInDomainDefinedAttributes(optional){if(optional===void 0){optional=false;}return new Sequence({optional,value:[new PrintableString(),new PrintableString()]});}function extensionAttributes(optional){if(optional===void 0){optional=false;}return new Set({optional,value:[new Primitive({optional:true,idBlock:{tagClass:3,tagNumber:0},isHexOnly:true}),new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:1},value:[new Any()]})]});}var GeneralName=/*#__PURE__*/function(_PkiObject3){_inheritsLoose(GeneralName,_PkiObject3);function GeneralName(parameters){var _this6;if(parameters===void 0){parameters={};}_this6=_PkiObject3.call(this)||this;_this6.type=getParametersValue(parameters,TYPE$4,GeneralName.defaultValues(TYPE$4));_this6.value=getParametersValue(parameters,VALUE$5,GeneralName.defaultValues(VALUE$5));if(parameters.schema){_this6.fromSchema(parameters.schema);}return _this6;}GeneralName.defaultValues=function defaultValues(memberName){switch(memberName){case TYPE$4:return 9;case VALUE$5:return {};default:return _PkiObject3.defaultValues.call(this,memberName);}};GeneralName.compareWithDefault=function compareWithDefault(memberName,memberValue){switch(memberName){case TYPE$4:return memberValue===GeneralName.defaultValues(memberName);case VALUE$5:return Object.keys(memberValue).length===0;default:return _PkiObject3.defaultValues.call(this,memberName);}};GeneralName.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Choice({value:[new Constructed({idBlock:{tagClass:3,tagNumber:0},name:names.blockName||EMPTY_STRING,value:[new ObjectIdentifier(),new Constructed({idBlock:{tagClass:3,tagNumber:0},value:[new Any()]})]}),new Primitive({name:names.blockName||EMPTY_STRING,idBlock:{tagClass:3,tagNumber:1}}),new Primitive({name:names.blockName||EMPTY_STRING,idBlock:{tagClass:3,tagNumber:2}}),new Constructed({idBlock:{tagClass:3,tagNumber:3},name:names.blockName||EMPTY_STRING,value:[builtInStandardAttributes(names.builtInStandardAttributes||{},false),builtInDomainDefinedAttributes(true),extensionAttributes(true)]}),new Constructed({idBlock:{tagClass:3,tagNumber:4},name:names.blockName||EMPTY_STRING,value:[RelativeDistinguishedNames.schema(names.directoryName||{})]}),new Constructed({idBlock:{tagClass:3,tagNumber:5},name:names.blockName||EMPTY_STRING,value:[new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:0},value:[new Choice({value:[new TeletexString(),new PrintableString(),new UniversalString(),new Utf8String(),new BmpString()]})]}),new Constructed({idBlock:{tagClass:3,tagNumber:1},value:[new Choice({value:[new TeletexString(),new PrintableString(),new UniversalString(),new Utf8String(),new BmpString()]})]})]}),new Primitive({name:names.blockName||EMPTY_STRING,idBlock:{tagClass:3,tagNumber:6}}),new Primitive({name:names.blockName||EMPTY_STRING,idBlock:{tagClass:3,tagNumber:7}}),new Primitive({name:names.blockName||EMPTY_STRING,idBlock:{tagClass:3,tagNumber:8}})]});};var _proto4=GeneralName.prototype;_proto4.fromSchema=function fromSchema(schema){clearProps(schema,["blockName","otherName","rfc822Name","dNSName","x400Address","directoryName","ediPartyName","uniformResourceIdentifier","iPAddress","registeredID"]);var asn1=compareSchema(schema,schema,GeneralName.schema({names:{blockName:"blockName",otherName:"otherName",rfc822Name:"rfc822Name",dNSName:"dNSName",x400Address:"x400Address",directoryName:{names:{blockName:"directoryName"}},ediPartyName:"ediPartyName",uniformResourceIdentifier:"uniformResourceIdentifier",iPAddress:"iPAddress",registeredID:"registeredID"}}));AsnError.assertSchema(asn1,this.className);this.type=asn1.result.blockName.idBlock.tagNumber;switch(this.type){case 0:this.value=asn1.result.blockName;break;case 1:case 2:case 6:{var value=asn1.result.blockName;value.idBlock.tagClass=1;value.idBlock.tagNumber=22;var valueBER=value.toBER(false);var asnValue=fromBER(valueBER);AsnError.assert(asnValue,"GeneralName value");this.value=asnValue.result.valueBlock.value;}break;case 3:this.value=asn1.result.blockName;break;case 4:this.value=new RelativeDistinguishedNames({schema:asn1.result.directoryName});break;case 5:this.value=asn1.result.ediPartyName;break;case 7:this.value=new OctetString({valueHex:asn1.result.blockName.valueBlock.valueHex});break;case 8:{var _value=asn1.result.blockName;_value.idBlock.tagClass=1;_value.idBlock.tagNumber=6;var _valueBER=_value.toBER(false);var _asnValue=fromBER(_valueBER);AsnError.assert(_asnValue,"GeneralName registeredID");this.value=_asnValue.result.valueBlock.toString();}break;}};_proto4.toSchema=function toSchema(){switch(this.type){case 0:case 3:case 5:return new Constructed({idBlock:{tagClass:3,tagNumber:this.type},value:[this.value]});case 1:case 2:case 6:{var value=new IA5String({value:this.value});value.idBlock.tagClass=3;value.idBlock.tagNumber=this.type;return value;}case 4:return new Constructed({idBlock:{tagClass:3,tagNumber:4},value:[this.value.toSchema()]});case 7:{var _value2=this.value;_value2.idBlock.tagClass=3;_value2.idBlock.tagNumber=this.type;return _value2;}case 8:{var _value3=new ObjectIdentifier({value:this.value});_value3.idBlock.tagClass=3;_value3.idBlock.tagNumber=this.type;return _value3;}default:return GeneralName.schema();}};_proto4.toJSON=function toJSON(){var _object={type:this.type,value:EMPTY_STRING};if(typeof this.value==="string")_object.value=this.value;else {try{_object.value=this.value.toJSON();}catch(ex){}}return _object;};return GeneralName;}(PkiObject);GeneralName.CLASS_NAME="GeneralName";var ACCESS_METHOD="accessMethod";var ACCESS_LOCATION="accessLocation";var CLEAR_PROPS$1v=[ACCESS_METHOD,ACCESS_LOCATION];var AccessDescription=/*#__PURE__*/function(_PkiObject4){_inheritsLoose(AccessDescription,_PkiObject4);function AccessDescription(parameters){var _this7;if(parameters===void 0){parameters={};}_this7=_PkiObject4.call(this)||this;_this7.accessMethod=getParametersValue(parameters,ACCESS_METHOD,AccessDescription.defaultValues(ACCESS_METHOD));_this7.accessLocation=getParametersValue(parameters,ACCESS_LOCATION,AccessDescription.defaultValues(ACCESS_LOCATION));if(parameters.schema){_this7.fromSchema(parameters.schema);}return _this7;}AccessDescription.defaultValues=function defaultValues(memberName){switch(memberName){case ACCESS_METHOD:return EMPTY_STRING;case ACCESS_LOCATION:return new GeneralName();default:return _PkiObject4.defaultValues.call(this,memberName);}};AccessDescription.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new ObjectIdentifier({name:names.accessMethod||EMPTY_STRING}),GeneralName.schema(names.accessLocation||{})]});};var _proto5=AccessDescription.prototype;_proto5.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1v);var asn1=compareSchema(schema,schema,AccessDescription.schema({names:{accessMethod:ACCESS_METHOD,accessLocation:{names:{blockName:ACCESS_LOCATION}}}}));AsnError.assertSchema(asn1,this.className);this.accessMethod=asn1.result.accessMethod.valueBlock.toString();this.accessLocation=new GeneralName({schema:asn1.result.accessLocation});};_proto5.toSchema=function toSchema(){return new Sequence({value:[new ObjectIdentifier({value:this.accessMethod}),this.accessLocation.toSchema()]});};_proto5.toJSON=function toJSON(){return {accessMethod:this.accessMethod,accessLocation:this.accessLocation.toJSON()};};return AccessDescription;}(PkiObject);AccessDescription.CLASS_NAME="AccessDescription";var ALGORITHM_ID="algorithmId";var ALGORITHM_PARAMS="algorithmParams";var ALGORITHM$2="algorithm";var PARAMS="params";var CLEAR_PROPS$1u=[ALGORITHM$2,PARAMS];var AlgorithmIdentifier=/*#__PURE__*/function(_PkiObject6){_inheritsLoose(AlgorithmIdentifier,_PkiObject6);function AlgorithmIdentifier(parameters){var _this9;if(parameters===void 0){parameters={};}_this9=_PkiObject6.call(this)||this;_this9.algorithmId=getParametersValue(parameters,ALGORITHM_ID,AlgorithmIdentifier.defaultValues(ALGORITHM_ID));if(ALGORITHM_PARAMS in parameters){_this9.algorithmParams=getParametersValue(parameters,ALGORITHM_PARAMS,AlgorithmIdentifier.defaultValues(ALGORITHM_PARAMS));}if(parameters.schema){_this9.fromSchema(parameters.schema);}return _this9;}AlgorithmIdentifier.defaultValues=function defaultValues(memberName){switch(memberName){case ALGORITHM_ID:return EMPTY_STRING;case ALGORITHM_PARAMS:return new Any();default:return _PkiObject6.defaultValues.call(this,memberName);}};AlgorithmIdentifier.compareWithDefault=function compareWithDefault(memberName,memberValue){switch(memberName){case ALGORITHM_ID:return memberValue===EMPTY_STRING;case ALGORITHM_PARAMS:return memberValue instanceof Any;default:return _PkiObject6.defaultValues.call(this,memberName);}};AlgorithmIdentifier.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,optional:names.optional||false,value:[new ObjectIdentifier({name:names.algorithmIdentifier||EMPTY_STRING}),new Any({name:names.algorithmParams||EMPTY_STRING,optional:true})]});};var _proto7=AlgorithmIdentifier.prototype;_proto7.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1u);var asn1=compareSchema(schema,schema,AlgorithmIdentifier.schema({names:{algorithmIdentifier:ALGORITHM$2,algorithmParams:PARAMS}}));AsnError.assertSchema(asn1,this.className);this.algorithmId=asn1.result.algorithm.valueBlock.toString();if(PARAMS in asn1.result){this.algorithmParams=asn1.result.params;}};_proto7.toSchema=function toSchema(){var outputArray=[];outputArray.push(new ObjectIdentifier({value:this.algorithmId}));if(this.algorithmParams&&!(this.algorithmParams instanceof Any)){outputArray.push(this.algorithmParams);}return new Sequence({value:outputArray});};_proto7.toJSON=function toJSON(){var object={algorithmId:this.algorithmId};if(this.algorithmParams&&!(this.algorithmParams instanceof Any)){object.algorithmParams=this.algorithmParams.toJSON();}return object;};_proto7.isEqual=function isEqual(algorithmIdentifier){if(!(algorithmIdentifier instanceof AlgorithmIdentifier)){return false;}if(this.algorithmId!==algorithmIdentifier.algorithmId){return false;}if(this.algorithmParams){if(algorithmIdentifier.algorithmParams){return JSON.stringify(this.algorithmParams)===JSON.stringify(algorithmIdentifier.algorithmParams);}return false;}if(algorithmIdentifier.algorithmParams){return false;}return true;};return AlgorithmIdentifier;}(PkiObject);AlgorithmIdentifier.CLASS_NAME="AlgorithmIdentifier";var ALT_NAMES="altNames";var CLEAR_PROPS$1t=[ALT_NAMES];var AltName=/*#__PURE__*/function(_PkiObject7){_inheritsLoose(AltName,_PkiObject7);function AltName(parameters){var _this10;if(parameters===void 0){parameters={};}_this10=_PkiObject7.call(this)||this;_this10.altNames=getParametersValue(parameters,ALT_NAMES,AltName.defaultValues(ALT_NAMES));if(parameters.schema){_this10.fromSchema(parameters.schema);}return _this10;}AltName.defaultValues=function defaultValues(memberName){switch(memberName){case ALT_NAMES:return [];default:return _PkiObject7.defaultValues.call(this,memberName);}};AltName.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Repeated({name:names.altNames||EMPTY_STRING,value:GeneralName.schema()})]});};var _proto8=AltName.prototype;_proto8.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1t);var asn1=compareSchema(schema,schema,AltName.schema({names:{altNames:ALT_NAMES}}));AsnError.assertSchema(asn1,this.className);if(ALT_NAMES in asn1.result){this.altNames=Array.from(asn1.result.altNames,element=>new GeneralName({schema:element}));}};_proto8.toSchema=function toSchema(){return new Sequence({value:Array.from(this.altNames,o=>o.toSchema())});};_proto8.toJSON=function toJSON(){return {altNames:Array.from(this.altNames,o=>o.toJSON())};};return AltName;}(PkiObject);AltName.CLASS_NAME="AltName";var TYPE$3="type";var VALUES$1="values";var CLEAR_PROPS$1s=[TYPE$3,VALUES$1];var Attribute=/*#__PURE__*/function(_PkiObject8){_inheritsLoose(Attribute,_PkiObject8);function Attribute(parameters){var _this11;if(parameters===void 0){parameters={};}_this11=_PkiObject8.call(this)||this;_this11.type=getParametersValue(parameters,TYPE$3,Attribute.defaultValues(TYPE$3));_this11.values=getParametersValue(parameters,VALUES$1,Attribute.defaultValues(VALUES$1));if(parameters.schema){_this11.fromSchema(parameters.schema);}return _this11;}Attribute.defaultValues=function defaultValues(memberName){switch(memberName){case TYPE$3:return EMPTY_STRING;case VALUES$1:return [];default:return _PkiObject8.defaultValues.call(this,memberName);}};Attribute.compareWithDefault=function compareWithDefault(memberName,memberValue){switch(memberName){case TYPE$3:return memberValue===EMPTY_STRING;case VALUES$1:return memberValue.length===0;default:return _PkiObject8.defaultValues.call(this,memberName);}};Attribute.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new ObjectIdentifier({name:names.type||EMPTY_STRING}),new Set({name:names.setName||EMPTY_STRING,value:[new Repeated({name:names.values||EMPTY_STRING,value:new Any()})]})]});};var _proto9=Attribute.prototype;_proto9.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1s);var asn1=compareSchema(schema,schema,Attribute.schema({names:{type:TYPE$3,values:VALUES$1}}));AsnError.assertSchema(asn1,this.className);this.type=asn1.result.type.valueBlock.toString();this.values=asn1.result.values;};_proto9.toSchema=function toSchema(){return new Sequence({value:[new ObjectIdentifier({value:this.type}),new Set({value:this.values})]});};_proto9.toJSON=function toJSON(){return {type:this.type,values:Array.from(this.values,o=>o.toJSON())};};return Attribute;}(PkiObject);Attribute.CLASS_NAME="Attribute";var NAMES="names";var GENERAL_NAMES="generalNames";var GeneralNames=/*#__PURE__*/function(_PkiObject10){_inheritsLoose(GeneralNames,_PkiObject10);function GeneralNames(parameters){var _this13;if(parameters===void 0){parameters={};}_this13=_PkiObject10.call(this)||this;_this13.names=getParametersValue(parameters,NAMES,GeneralNames.defaultValues(NAMES));if(parameters.schema){_this13.fromSchema(parameters.schema);}return _this13;}GeneralNames.defaultValues=function defaultValues(memberName){switch(memberName){case"names":return [];default:return _PkiObject10.defaultValues.call(this,memberName);}};GeneralNames.schema=function schema(parameters,optional){if(parameters===void 0){parameters={};}if(optional===void 0){optional=false;}var names=getParametersValue(parameters,NAMES,{});return new Sequence({optional,name:names.blockName||EMPTY_STRING,value:[new Repeated({name:names.generalNames||EMPTY_STRING,value:GeneralName.schema()})]});};var _proto11=GeneralNames.prototype;_proto11.fromSchema=function fromSchema(schema){clearProps(schema,[NAMES,GENERAL_NAMES]);var asn1=compareSchema(schema,schema,GeneralNames.schema({names:{blockName:NAMES,generalNames:GENERAL_NAMES}}));AsnError.assertSchema(asn1,this.className);this.names=Array.from(asn1.result.generalNames,element=>new GeneralName({schema:element}));};_proto11.toSchema=function toSchema(){return new Sequence({value:Array.from(this.names,o=>o.toSchema())});};_proto11.toJSON=function toJSON(){return {names:Array.from(this.names,o=>o.toJSON())};};return GeneralNames;}(PkiObject);GeneralNames.CLASS_NAME="GeneralNames";var id_SubjectDirectoryAttributes="2.5.29.9";var id_PrivateKeyUsagePeriod="2.5.29.16";var id_SubjectAltName="2.5.29.17";var id_IssuerAltName="2.5.29.18";var id_BasicConstraints="2.5.29.19";var id_IssuingDistributionPoint="2.5.29.28";var id_CertificateIssuer="2.5.29.29";var id_NameConstraints="2.5.29.30";var id_CRLDistributionPoints="2.5.29.31";var id_FreshestCRL="2.5.29.46";var id_CertificatePolicies="2.5.29.32";var id_MicrosoftAppPolicies="1.3.6.1.4.1.311.21.10";var id_PolicyMappings="2.5.29.33";var id_AuthorityKeyIdentifier="2.5.29.35";var id_PolicyConstraints="2.5.29.36";var id_ExtKeyUsage="2.5.29.37";var id_AuthorityInfoAccess="1.3.6.1.5.5.7.1.1";var id_SubjectInfoAccess="1.3.6.1.5.5.7.1.11";var id_SignedCertificateTimestampList="1.3.6.1.4.1.11129.2.4.2";var id_MicrosoftCertTemplateV2="1.3.6.1.4.1.311.21.7";var id_MicrosoftCaVersion="1.3.6.1.4.1.311.21.1";var id_QCStatements="1.3.6.1.5.5.7.1.3";var KEY_IDENTIFIER$1="keyIdentifier";var AUTHORITY_CERT_ISSUER="authorityCertIssuer";var AUTHORITY_CERT_SERIAL_NUMBER="authorityCertSerialNumber";var CLEAR_PROPS$1q=[KEY_IDENTIFIER$1,AUTHORITY_CERT_ISSUER,AUTHORITY_CERT_SERIAL_NUMBER];var AuthorityKeyIdentifier=/*#__PURE__*/function(_PkiObject11){_inheritsLoose(AuthorityKeyIdentifier,_PkiObject11);function AuthorityKeyIdentifier(parameters){var _this14;if(parameters===void 0){parameters={};}_this14=_PkiObject11.call(this)||this;if(KEY_IDENTIFIER$1 in parameters){_this14.keyIdentifier=getParametersValue(parameters,KEY_IDENTIFIER$1,AuthorityKeyIdentifier.defaultValues(KEY_IDENTIFIER$1));}if(AUTHORITY_CERT_ISSUER in parameters){_this14.authorityCertIssuer=getParametersValue(parameters,AUTHORITY_CERT_ISSUER,AuthorityKeyIdentifier.defaultValues(AUTHORITY_CERT_ISSUER));}if(AUTHORITY_CERT_SERIAL_NUMBER in parameters){_this14.authorityCertSerialNumber=getParametersValue(parameters,AUTHORITY_CERT_SERIAL_NUMBER,AuthorityKeyIdentifier.defaultValues(AUTHORITY_CERT_SERIAL_NUMBER));}if(parameters.schema){_this14.fromSchema(parameters.schema);}return _this14;}AuthorityKeyIdentifier.defaultValues=function defaultValues(memberName){switch(memberName){case KEY_IDENTIFIER$1:return new OctetString();case AUTHORITY_CERT_ISSUER:return [];case AUTHORITY_CERT_SERIAL_NUMBER:return new Integer();default:return _PkiObject11.defaultValues.call(this,memberName);}};AuthorityKeyIdentifier.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Primitive({name:names.keyIdentifier||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:0}}),new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:1},value:[new Repeated({name:names.authorityCertIssuer||EMPTY_STRING,value:GeneralName.schema()})]}),new Primitive({name:names.authorityCertSerialNumber||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:2}})]});};var _proto12=AuthorityKeyIdentifier.prototype;_proto12.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1q);var asn1=compareSchema(schema,schema,AuthorityKeyIdentifier.schema({names:{keyIdentifier:KEY_IDENTIFIER$1,authorityCertIssuer:AUTHORITY_CERT_ISSUER,authorityCertSerialNumber:AUTHORITY_CERT_SERIAL_NUMBER}}));AsnError.assertSchema(asn1,this.className);if(KEY_IDENTIFIER$1 in asn1.result)this.keyIdentifier=new OctetString({valueHex:asn1.result.keyIdentifier.valueBlock.valueHex});if(AUTHORITY_CERT_ISSUER in asn1.result)this.authorityCertIssuer=Array.from(asn1.result.authorityCertIssuer,o=>new GeneralName({schema:o}));if(AUTHORITY_CERT_SERIAL_NUMBER in asn1.result)this.authorityCertSerialNumber=new Integer({valueHex:asn1.result.authorityCertSerialNumber.valueBlock.valueHex});};_proto12.toSchema=function toSchema(){var outputArray=[];if(this.keyIdentifier){outputArray.push(new Primitive({idBlock:{tagClass:3,tagNumber:0},valueHex:this.keyIdentifier.valueBlock.valueHexView}));}if(this.authorityCertIssuer){outputArray.push(new Constructed({idBlock:{tagClass:3,tagNumber:1},value:Array.from(this.authorityCertIssuer,o=>o.toSchema())}));}if(this.authorityCertSerialNumber){outputArray.push(new Primitive({idBlock:{tagClass:3,tagNumber:2},valueHex:this.authorityCertSerialNumber.valueBlock.valueHexView}));}return new Sequence({value:outputArray});};_proto12.toJSON=function toJSON(){var object={};if(this.keyIdentifier){object.keyIdentifier=this.keyIdentifier.toJSON();}if(this.authorityCertIssuer){object.authorityCertIssuer=Array.from(this.authorityCertIssuer,o=>o.toJSON());}if(this.authorityCertSerialNumber){object.authorityCertSerialNumber=this.authorityCertSerialNumber.toJSON();}return object;};return AuthorityKeyIdentifier;}(PkiObject);AuthorityKeyIdentifier.CLASS_NAME="AuthorityKeyIdentifier";var PATH_LENGTH_CONSTRAINT="pathLenConstraint";var CA="cA";var BasicConstraints=/*#__PURE__*/function(_PkiObject12){_inheritsLoose(BasicConstraints,_PkiObject12);function BasicConstraints(parameters){var _this15;if(parameters===void 0){parameters={};}_this15=_PkiObject12.call(this)||this;_this15.cA=getParametersValue(parameters,CA,false);if(PATH_LENGTH_CONSTRAINT in parameters){_this15.pathLenConstraint=getParametersValue(parameters,PATH_LENGTH_CONSTRAINT,0);}if(parameters.schema){_this15.fromSchema(parameters.schema);}return _this15;}BasicConstraints.defaultValues=function defaultValues(memberName){switch(memberName){case CA:return false;default:return _PkiObject12.defaultValues.call(this,memberName);}};BasicConstraints.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Boolean$1({optional:true,name:names.cA||EMPTY_STRING}),new Integer({optional:true,name:names.pathLenConstraint||EMPTY_STRING})]});};var _proto13=BasicConstraints.prototype;_proto13.fromSchema=function fromSchema(schema){clearProps(schema,[CA,PATH_LENGTH_CONSTRAINT]);var asn1=compareSchema(schema,schema,BasicConstraints.schema({names:{cA:CA,pathLenConstraint:PATH_LENGTH_CONSTRAINT}}));AsnError.assertSchema(asn1,this.className);if(CA in asn1.result){this.cA=asn1.result.cA.valueBlock.value;}if(PATH_LENGTH_CONSTRAINT in asn1.result){if(asn1.result.pathLenConstraint.valueBlock.isHexOnly){this.pathLenConstraint=asn1.result.pathLenConstraint;}else {this.pathLenConstraint=asn1.result.pathLenConstraint.valueBlock.valueDec;}}};_proto13.toSchema=function toSchema(){var outputArray=[];if(this.cA!==BasicConstraints.defaultValues(CA))outputArray.push(new Boolean$1({value:this.cA}));if(PATH_LENGTH_CONSTRAINT in this){if(this.pathLenConstraint instanceof Integer){outputArray.push(this.pathLenConstraint);}else {outputArray.push(new Integer({value:this.pathLenConstraint}));}}return new Sequence({value:outputArray});};_proto13.toJSON=function toJSON(){var object={};if(this.cA!==BasicConstraints.defaultValues(CA)){object.cA=this.cA;}if(PATH_LENGTH_CONSTRAINT in this){if(this.pathLenConstraint instanceof Integer){object.pathLenConstraint=this.pathLenConstraint.toJSON();}else {object.pathLenConstraint=this.pathLenConstraint;}}return object;};return BasicConstraints;}(PkiObject);BasicConstraints.CLASS_NAME="BasicConstraints";var CERTIFICATE_INDEX="certificateIndex";var KEY_INDEX="keyIndex";var CAVersion=/*#__PURE__*/function(_PkiObject13){_inheritsLoose(CAVersion,_PkiObject13);function CAVersion(parameters){var _this16;if(parameters===void 0){parameters={};}_this16=_PkiObject13.call(this)||this;_this16.certificateIndex=getParametersValue(parameters,CERTIFICATE_INDEX,CAVersion.defaultValues(CERTIFICATE_INDEX));_this16.keyIndex=getParametersValue(parameters,KEY_INDEX,CAVersion.defaultValues(KEY_INDEX));if(parameters.schema){_this16.fromSchema(parameters.schema);}return _this16;}CAVersion.defaultValues=function defaultValues(memberName){switch(memberName){case CERTIFICATE_INDEX:case KEY_INDEX:return 0;default:return _PkiObject13.defaultValues.call(this,memberName);}};CAVersion.schema=function schema(){return new Integer();};var _proto14=CAVersion.prototype;_proto14.fromSchema=function fromSchema(schema){if(schema.constructor.blockName()!==Integer.blockName()){throw new Error("Object's schema was not verified against input data for CAVersion");}var value=schema.valueBlock.valueHex.slice(0);var valueView=new Uint8Array(value);switch(true){case value.byteLength<4:{var tempValue=new ArrayBuffer(4);var tempValueView=new Uint8Array(tempValue);tempValueView.set(valueView,4-value.byteLength);value=tempValue.slice(0);}break;case value.byteLength>4:{var _tempValue=new ArrayBuffer(4);var _tempValueView=new Uint8Array(_tempValue);_tempValueView.set(valueView.slice(0,4));value=_tempValue.slice(0);}break;}var keyIndexBuffer=value.slice(0,2);var keyIndexView8=new Uint8Array(keyIndexBuffer);var temp=keyIndexView8[0];keyIndexView8[0]=keyIndexView8[1];keyIndexView8[1]=temp;var keyIndexView16=new Uint16Array(keyIndexBuffer);this.keyIndex=keyIndexView16[0];var certificateIndexBuffer=value.slice(2);var certificateIndexView8=new Uint8Array(certificateIndexBuffer);temp=certificateIndexView8[0];certificateIndexView8[0]=certificateIndexView8[1];certificateIndexView8[1]=temp;var certificateIndexView16=new Uint16Array(certificateIndexBuffer);this.certificateIndex=certificateIndexView16[0];};_proto14.toSchema=function toSchema(){var certificateIndexBuffer=new ArrayBuffer(2);var certificateIndexView=new Uint16Array(certificateIndexBuffer);certificateIndexView[0]=this.certificateIndex;var certificateIndexView8=new Uint8Array(certificateIndexBuffer);var temp=certificateIndexView8[0];certificateIndexView8[0]=certificateIndexView8[1];certificateIndexView8[1]=temp;var keyIndexBuffer=new ArrayBuffer(2);var keyIndexView=new Uint16Array(keyIndexBuffer);keyIndexView[0]=this.keyIndex;var keyIndexView8=new Uint8Array(keyIndexBuffer);temp=keyIndexView8[0];keyIndexView8[0]=keyIndexView8[1];keyIndexView8[1]=temp;return new Integer({valueHex:utilConcatBuf(keyIndexBuffer,certificateIndexBuffer)});};_proto14.toJSON=function toJSON(){return {certificateIndex:this.certificateIndex,keyIndex:this.keyIndex};};return CAVersion;}(PkiObject);CAVersion.CLASS_NAME="CAVersion";var POLICY_QUALIFIER_ID="policyQualifierId";var QUALIFIER="qualifier";var CLEAR_PROPS$1p=[POLICY_QUALIFIER_ID,QUALIFIER];var PolicyQualifierInfo=/*#__PURE__*/function(_PkiObject14){_inheritsLoose(PolicyQualifierInfo,_PkiObject14);function PolicyQualifierInfo(parameters){var _this17;if(parameters===void 0){parameters={};}_this17=_PkiObject14.call(this)||this;_this17.policyQualifierId=getParametersValue(parameters,POLICY_QUALIFIER_ID,PolicyQualifierInfo.defaultValues(POLICY_QUALIFIER_ID));_this17.qualifier=getParametersValue(parameters,QUALIFIER,PolicyQualifierInfo.defaultValues(QUALIFIER));if(parameters.schema){_this17.fromSchema(parameters.schema);}return _this17;}PolicyQualifierInfo.defaultValues=function defaultValues(memberName){switch(memberName){case POLICY_QUALIFIER_ID:return EMPTY_STRING;case QUALIFIER:return new Any();default:return _PkiObject14.defaultValues.call(this,memberName);}};PolicyQualifierInfo.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new ObjectIdentifier({name:names.policyQualifierId||EMPTY_STRING}),new Any({name:names.qualifier||EMPTY_STRING})]});};var _proto15=PolicyQualifierInfo.prototype;_proto15.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1p);var asn1=compareSchema(schema,schema,PolicyQualifierInfo.schema({names:{policyQualifierId:POLICY_QUALIFIER_ID,qualifier:QUALIFIER}}));AsnError.assertSchema(asn1,this.className);this.policyQualifierId=asn1.result.policyQualifierId.valueBlock.toString();this.qualifier=asn1.result.qualifier;};_proto15.toSchema=function toSchema(){return new Sequence({value:[new ObjectIdentifier({value:this.policyQualifierId}),this.qualifier]});};_proto15.toJSON=function toJSON(){return {policyQualifierId:this.policyQualifierId,qualifier:this.qualifier.toJSON()};};return PolicyQualifierInfo;}(PkiObject);PolicyQualifierInfo.CLASS_NAME="PolicyQualifierInfo";var POLICY_IDENTIFIER="policyIdentifier";var POLICY_QUALIFIERS="policyQualifiers";var CLEAR_PROPS$1o=[POLICY_IDENTIFIER,POLICY_QUALIFIERS];var PolicyInformation=/*#__PURE__*/function(_PkiObject15){_inheritsLoose(PolicyInformation,_PkiObject15);function PolicyInformation(parameters){var _this18;if(parameters===void 0){parameters={};}_this18=_PkiObject15.call(this)||this;_this18.policyIdentifier=getParametersValue(parameters,POLICY_IDENTIFIER,PolicyInformation.defaultValues(POLICY_IDENTIFIER));if(POLICY_QUALIFIERS in parameters){_this18.policyQualifiers=getParametersValue(parameters,POLICY_QUALIFIERS,PolicyInformation.defaultValues(POLICY_QUALIFIERS));}if(parameters.schema){_this18.fromSchema(parameters.schema);}return _this18;}PolicyInformation.defaultValues=function defaultValues(memberName){switch(memberName){case POLICY_IDENTIFIER:return EMPTY_STRING;case POLICY_QUALIFIERS:return [];default:return _PkiObject15.defaultValues.call(this,memberName);}};PolicyInformation.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new ObjectIdentifier({name:names.policyIdentifier||EMPTY_STRING}),new Sequence({optional:true,value:[new Repeated({name:names.policyQualifiers||EMPTY_STRING,value:PolicyQualifierInfo.schema()})]})]});};var _proto16=PolicyInformation.prototype;_proto16.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1o);var asn1=compareSchema(schema,schema,PolicyInformation.schema({names:{policyIdentifier:POLICY_IDENTIFIER,policyQualifiers:POLICY_QUALIFIERS}}));AsnError.assertSchema(asn1,this.className);this.policyIdentifier=asn1.result.policyIdentifier.valueBlock.toString();if(POLICY_QUALIFIERS in asn1.result){this.policyQualifiers=Array.from(asn1.result.policyQualifiers,element=>new PolicyQualifierInfo({schema:element}));}};_proto16.toSchema=function toSchema(){var outputArray=[];outputArray.push(new ObjectIdentifier({value:this.policyIdentifier}));if(this.policyQualifiers){outputArray.push(new Sequence({value:Array.from(this.policyQualifiers,o=>o.toSchema())}));}return new Sequence({value:outputArray});};_proto16.toJSON=function toJSON(){var res={policyIdentifier:this.policyIdentifier};if(this.policyQualifiers)res.policyQualifiers=Array.from(this.policyQualifiers,o=>o.toJSON());return res;};return PolicyInformation;}(PkiObject);PolicyInformation.CLASS_NAME="PolicyInformation";var CERTIFICATE_POLICIES="certificatePolicies";var CLEAR_PROPS$1n=[CERTIFICATE_POLICIES];var CertificatePolicies=/*#__PURE__*/function(_PkiObject16){_inheritsLoose(CertificatePolicies,_PkiObject16);function CertificatePolicies(parameters){var _this19;if(parameters===void 0){parameters={};}_this19=_PkiObject16.call(this)||this;_this19.certificatePolicies=getParametersValue(parameters,CERTIFICATE_POLICIES,CertificatePolicies.defaultValues(CERTIFICATE_POLICIES));if(parameters.schema){_this19.fromSchema(parameters.schema);}return _this19;}CertificatePolicies.defaultValues=function defaultValues(memberName){switch(memberName){case CERTIFICATE_POLICIES:return [];default:return _PkiObject16.defaultValues.call(this,memberName);}};CertificatePolicies.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Repeated({name:names.certificatePolicies||EMPTY_STRING,value:PolicyInformation.schema()})]});};var _proto17=CertificatePolicies.prototype;_proto17.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1n);var asn1=compareSchema(schema,schema,CertificatePolicies.schema({names:{certificatePolicies:CERTIFICATE_POLICIES}}));AsnError.assertSchema(asn1,this.className);this.certificatePolicies=Array.from(asn1.result.certificatePolicies,element=>new PolicyInformation({schema:element}));};_proto17.toSchema=function toSchema(){return new Sequence({value:Array.from(this.certificatePolicies,o=>o.toSchema())});};_proto17.toJSON=function toJSON(){return {certificatePolicies:Array.from(this.certificatePolicies,o=>o.toJSON())};};return CertificatePolicies;}(PkiObject);CertificatePolicies.CLASS_NAME="CertificatePolicies";var TEMPLATE_ID="templateID";var TEMPLATE_MAJOR_VERSION="templateMajorVersion";var TEMPLATE_MINOR_VERSION="templateMinorVersion";var CLEAR_PROPS$1m=[TEMPLATE_ID,TEMPLATE_MAJOR_VERSION,TEMPLATE_MINOR_VERSION];var CertificateTemplate=/*#__PURE__*/function(_PkiObject17){_inheritsLoose(CertificateTemplate,_PkiObject17);function CertificateTemplate(parameters){var _this20;if(parameters===void 0){parameters={};}_this20=_PkiObject17.call(this)||this;_this20.templateID=getParametersValue(parameters,TEMPLATE_ID,CertificateTemplate.defaultValues(TEMPLATE_ID));if(TEMPLATE_MAJOR_VERSION in parameters){_this20.templateMajorVersion=getParametersValue(parameters,TEMPLATE_MAJOR_VERSION,CertificateTemplate.defaultValues(TEMPLATE_MAJOR_VERSION));}if(TEMPLATE_MINOR_VERSION in parameters){_this20.templateMinorVersion=getParametersValue(parameters,TEMPLATE_MINOR_VERSION,CertificateTemplate.defaultValues(TEMPLATE_MINOR_VERSION));}if(parameters.schema){_this20.fromSchema(parameters.schema);}return _this20;}CertificateTemplate.defaultValues=function defaultValues(memberName){switch(memberName){case TEMPLATE_ID:return EMPTY_STRING;case TEMPLATE_MAJOR_VERSION:case TEMPLATE_MINOR_VERSION:return 0;default:return _PkiObject17.defaultValues.call(this,memberName);}};CertificateTemplate.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new ObjectIdentifier({name:names.templateID||EMPTY_STRING}),new Integer({name:names.templateMajorVersion||EMPTY_STRING,optional:true}),new Integer({name:names.templateMinorVersion||EMPTY_STRING,optional:true})]});};var _proto18=CertificateTemplate.prototype;_proto18.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1m);var asn1=compareSchema(schema,schema,CertificateTemplate.schema({names:{templateID:TEMPLATE_ID,templateMajorVersion:TEMPLATE_MAJOR_VERSION,templateMinorVersion:TEMPLATE_MINOR_VERSION}}));AsnError.assertSchema(asn1,this.className);this.templateID=asn1.result.templateID.valueBlock.toString();if(TEMPLATE_MAJOR_VERSION in asn1.result){this.templateMajorVersion=asn1.result.templateMajorVersion.valueBlock.valueDec;}if(TEMPLATE_MINOR_VERSION in asn1.result){this.templateMinorVersion=asn1.result.templateMinorVersion.valueBlock.valueDec;}};_proto18.toSchema=function toSchema(){var outputArray=[];outputArray.push(new ObjectIdentifier({value:this.templateID}));if(TEMPLATE_MAJOR_VERSION in this){outputArray.push(new Integer({value:this.templateMajorVersion}));}if(TEMPLATE_MINOR_VERSION in this){outputArray.push(new Integer({value:this.templateMinorVersion}));}return new Sequence({value:outputArray});};_proto18.toJSON=function toJSON(){var res={templateID:this.templateID};if(TEMPLATE_MAJOR_VERSION in this)res.templateMajorVersion=this.templateMajorVersion;if(TEMPLATE_MINOR_VERSION in this)res.templateMinorVersion=this.templateMinorVersion;return res;};return CertificateTemplate;}(PkiObject);var DISTRIBUTION_POINT$1="distributionPoint";var DISTRIBUTION_POINT_NAMES$1="distributionPointNames";var REASONS="reasons";var CRL_ISSUER="cRLIssuer";var CRL_ISSUER_NAMES="cRLIssuerNames";var CLEAR_PROPS$1l=[DISTRIBUTION_POINT$1,DISTRIBUTION_POINT_NAMES$1,REASONS,CRL_ISSUER,CRL_ISSUER_NAMES];var DistributionPoint=/*#__PURE__*/function(_PkiObject18){_inheritsLoose(DistributionPoint,_PkiObject18);function DistributionPoint(parameters){var _this21;if(parameters===void 0){parameters={};}_this21=_PkiObject18.call(this)||this;if(DISTRIBUTION_POINT$1 in parameters){_this21.distributionPoint=getParametersValue(parameters,DISTRIBUTION_POINT$1,DistributionPoint.defaultValues(DISTRIBUTION_POINT$1));}if(REASONS in parameters){_this21.reasons=getParametersValue(parameters,REASONS,DistributionPoint.defaultValues(REASONS));}if(CRL_ISSUER in parameters){_this21.cRLIssuer=getParametersValue(parameters,CRL_ISSUER,DistributionPoint.defaultValues(CRL_ISSUER));}if(parameters.schema){_this21.fromSchema(parameters.schema);}return _this21;}DistributionPoint.defaultValues=function defaultValues(memberName){switch(memberName){case DISTRIBUTION_POINT$1:return [];case REASONS:return new BitString();case CRL_ISSUER:return [];default:return _PkiObject18.defaultValues.call(this,memberName);}};DistributionPoint.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:0},value:[new Choice({value:[new Constructed({name:names.distributionPoint||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:0},value:[new Repeated({name:names.distributionPointNames||EMPTY_STRING,value:GeneralName.schema()})]}),new Constructed({name:names.distributionPoint||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:1},value:RelativeDistinguishedNames.schema().valueBlock.value})]})]}),new Primitive({name:names.reasons||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:1}}),new Constructed({name:names.cRLIssuer||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:2},value:[new Repeated({name:names.cRLIssuerNames||EMPTY_STRING,value:GeneralName.schema()})]})]});};var _proto19=DistributionPoint.prototype;_proto19.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1l);var asn1=compareSchema(schema,schema,DistributionPoint.schema({names:{distributionPoint:DISTRIBUTION_POINT$1,distributionPointNames:DISTRIBUTION_POINT_NAMES$1,reasons:REASONS,cRLIssuer:CRL_ISSUER,cRLIssuerNames:CRL_ISSUER_NAMES}}));AsnError.assertSchema(asn1,this.className);if(DISTRIBUTION_POINT$1 in asn1.result){if(asn1.result.distributionPoint.idBlock.tagNumber===0){this.distributionPoint=Array.from(asn1.result.distributionPointNames,element=>new GeneralName({schema:element}));}if(asn1.result.distributionPoint.idBlock.tagNumber===1){this.distributionPoint=new RelativeDistinguishedNames({schema:new Sequence({value:asn1.result.distributionPoint.valueBlock.value})});}}if(REASONS in asn1.result){this.reasons=new BitString({valueHex:asn1.result.reasons.valueBlock.valueHex});}if(CRL_ISSUER in asn1.result){this.cRLIssuer=Array.from(asn1.result.cRLIssuerNames,element=>new GeneralName({schema:element}));}};_proto19.toSchema=function toSchema(){var outputArray=[];if(this.distributionPoint){var internalValue;if(this.distributionPoint instanceof Array){internalValue=new Constructed({idBlock:{tagClass:3,tagNumber:0},value:Array.from(this.distributionPoint,o=>o.toSchema())});}else {internalValue=new Constructed({idBlock:{tagClass:3,tagNumber:1},value:[this.distributionPoint.toSchema()]});}outputArray.push(new Constructed({idBlock:{tagClass:3,tagNumber:0},value:[internalValue]}));}if(this.reasons){outputArray.push(new Primitive({idBlock:{tagClass:3,tagNumber:1},valueHex:this.reasons.valueBlock.valueHexView}));}if(this.cRLIssuer){outputArray.push(new Constructed({idBlock:{tagClass:3,tagNumber:2},value:Array.from(this.cRLIssuer,o=>o.toSchema())}));}return new Sequence({value:outputArray});};_proto19.toJSON=function toJSON(){var object={};if(this.distributionPoint){if(this.distributionPoint instanceof Array){object.distributionPoint=Array.from(this.distributionPoint,o=>o.toJSON());}else {object.distributionPoint=this.distributionPoint.toJSON();}}if(this.reasons){object.reasons=this.reasons.toJSON();}if(this.cRLIssuer){object.cRLIssuer=Array.from(this.cRLIssuer,o=>o.toJSON());}return object;};return DistributionPoint;}(PkiObject);DistributionPoint.CLASS_NAME="DistributionPoint";var DISTRIBUTION_POINTS="distributionPoints";var CLEAR_PROPS$1k=[DISTRIBUTION_POINTS];var CRLDistributionPoints=/*#__PURE__*/function(_PkiObject19){_inheritsLoose(CRLDistributionPoints,_PkiObject19);function CRLDistributionPoints(parameters){var _this22;if(parameters===void 0){parameters={};}_this22=_PkiObject19.call(this)||this;_this22.distributionPoints=getParametersValue(parameters,DISTRIBUTION_POINTS,CRLDistributionPoints.defaultValues(DISTRIBUTION_POINTS));if(parameters.schema){_this22.fromSchema(parameters.schema);}return _this22;}CRLDistributionPoints.defaultValues=function defaultValues(memberName){switch(memberName){case DISTRIBUTION_POINTS:return [];default:return _PkiObject19.defaultValues.call(this,memberName);}};CRLDistributionPoints.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Repeated({name:names.distributionPoints||EMPTY_STRING,value:DistributionPoint.schema()})]});};var _proto20=CRLDistributionPoints.prototype;_proto20.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1k);var asn1=compareSchema(schema,schema,CRLDistributionPoints.schema({names:{distributionPoints:DISTRIBUTION_POINTS}}));AsnError.assertSchema(asn1,this.className);this.distributionPoints=Array.from(asn1.result.distributionPoints,element=>new DistributionPoint({schema:element}));};_proto20.toSchema=function toSchema(){return new Sequence({value:Array.from(this.distributionPoints,o=>o.toSchema())});};_proto20.toJSON=function toJSON(){return {distributionPoints:Array.from(this.distributionPoints,o=>o.toJSON())};};return CRLDistributionPoints;}(PkiObject);CRLDistributionPoints.CLASS_NAME="CRLDistributionPoints";var KEY_PURPOSES="keyPurposes";var CLEAR_PROPS$1j=[KEY_PURPOSES];var ExtKeyUsage=/*#__PURE__*/function(_PkiObject20){_inheritsLoose(ExtKeyUsage,_PkiObject20);function ExtKeyUsage(parameters){var _this23;if(parameters===void 0){parameters={};}_this23=_PkiObject20.call(this)||this;_this23.keyPurposes=getParametersValue(parameters,KEY_PURPOSES,ExtKeyUsage.defaultValues(KEY_PURPOSES));if(parameters.schema){_this23.fromSchema(parameters.schema);}return _this23;}ExtKeyUsage.defaultValues=function defaultValues(memberName){switch(memberName){case KEY_PURPOSES:return [];default:return _PkiObject20.defaultValues.call(this,memberName);}};ExtKeyUsage.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Repeated({name:names.keyPurposes||EMPTY_STRING,value:new ObjectIdentifier()})]});};var _proto21=ExtKeyUsage.prototype;_proto21.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1j);var asn1=compareSchema(schema,schema,ExtKeyUsage.schema({names:{keyPurposes:KEY_PURPOSES}}));AsnError.assertSchema(asn1,this.className);this.keyPurposes=Array.from(asn1.result.keyPurposes,element=>element.valueBlock.toString());};_proto21.toSchema=function toSchema(){return new Sequence({value:Array.from(this.keyPurposes,element=>new ObjectIdentifier({value:element}))});};_proto21.toJSON=function toJSON(){return {keyPurposes:Array.from(this.keyPurposes)};};return ExtKeyUsage;}(PkiObject);ExtKeyUsage.CLASS_NAME="ExtKeyUsage";var ACCESS_DESCRIPTIONS="accessDescriptions";var InfoAccess=/*#__PURE__*/function(_PkiObject21){_inheritsLoose(InfoAccess,_PkiObject21);function InfoAccess(parameters){var _this24;if(parameters===void 0){parameters={};}_this24=_PkiObject21.call(this)||this;_this24.accessDescriptions=getParametersValue(parameters,ACCESS_DESCRIPTIONS,InfoAccess.defaultValues(ACCESS_DESCRIPTIONS));if(parameters.schema){_this24.fromSchema(parameters.schema);}return _this24;}InfoAccess.defaultValues=function defaultValues(memberName){switch(memberName){case ACCESS_DESCRIPTIONS:return [];default:return _PkiObject21.defaultValues.call(this,memberName);}};InfoAccess.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Repeated({name:names.accessDescriptions||EMPTY_STRING,value:AccessDescription.schema()})]});};var _proto22=InfoAccess.prototype;_proto22.fromSchema=function fromSchema(schema){clearProps(schema,[ACCESS_DESCRIPTIONS]);var asn1=compareSchema(schema,schema,InfoAccess.schema({names:{accessDescriptions:ACCESS_DESCRIPTIONS}}));AsnError.assertSchema(asn1,this.className);this.accessDescriptions=Array.from(asn1.result.accessDescriptions,element=>new AccessDescription({schema:element}));};_proto22.toSchema=function toSchema(){return new Sequence({value:Array.from(this.accessDescriptions,o=>o.toSchema())});};_proto22.toJSON=function toJSON(){return {accessDescriptions:Array.from(this.accessDescriptions,o=>o.toJSON())};};return InfoAccess;}(PkiObject);InfoAccess.CLASS_NAME="InfoAccess";var DISTRIBUTION_POINT="distributionPoint";var DISTRIBUTION_POINT_NAMES="distributionPointNames";var ONLY_CONTAINS_USER_CERTS="onlyContainsUserCerts";var ONLY_CONTAINS_CA_CERTS="onlyContainsCACerts";var ONLY_SOME_REASON="onlySomeReasons";var INDIRECT_CRL="indirectCRL";var ONLY_CONTAINS_ATTRIBUTE_CERTS="onlyContainsAttributeCerts";var CLEAR_PROPS$1i=[DISTRIBUTION_POINT,DISTRIBUTION_POINT_NAMES,ONLY_CONTAINS_USER_CERTS,ONLY_CONTAINS_CA_CERTS,ONLY_SOME_REASON,INDIRECT_CRL,ONLY_CONTAINS_ATTRIBUTE_CERTS];var IssuingDistributionPoint=/*#__PURE__*/function(_PkiObject22){_inheritsLoose(IssuingDistributionPoint,_PkiObject22);function IssuingDistributionPoint(parameters){var _this25;if(parameters===void 0){parameters={};}_this25=_PkiObject22.call(this)||this;if(DISTRIBUTION_POINT in parameters){_this25.distributionPoint=getParametersValue(parameters,DISTRIBUTION_POINT,IssuingDistributionPoint.defaultValues(DISTRIBUTION_POINT));}_this25.onlyContainsUserCerts=getParametersValue(parameters,ONLY_CONTAINS_USER_CERTS,IssuingDistributionPoint.defaultValues(ONLY_CONTAINS_USER_CERTS));_this25.onlyContainsCACerts=getParametersValue(parameters,ONLY_CONTAINS_CA_CERTS,IssuingDistributionPoint.defaultValues(ONLY_CONTAINS_CA_CERTS));if(ONLY_SOME_REASON in parameters){_this25.onlySomeReasons=getParametersValue(parameters,ONLY_SOME_REASON,IssuingDistributionPoint.defaultValues(ONLY_SOME_REASON));}_this25.indirectCRL=getParametersValue(parameters,INDIRECT_CRL,IssuingDistributionPoint.defaultValues(INDIRECT_CRL));_this25.onlyContainsAttributeCerts=getParametersValue(parameters,ONLY_CONTAINS_ATTRIBUTE_CERTS,IssuingDistributionPoint.defaultValues(ONLY_CONTAINS_ATTRIBUTE_CERTS));if(parameters.schema){_this25.fromSchema(parameters.schema);}return _this25;}IssuingDistributionPoint.defaultValues=function defaultValues(memberName){switch(memberName){case DISTRIBUTION_POINT:return [];case ONLY_CONTAINS_USER_CERTS:return false;case ONLY_CONTAINS_CA_CERTS:return false;case ONLY_SOME_REASON:return 0;case INDIRECT_CRL:return false;case ONLY_CONTAINS_ATTRIBUTE_CERTS:return false;default:return _PkiObject22.defaultValues.call(this,memberName);}};IssuingDistributionPoint.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:0},value:[new Choice({value:[new Constructed({name:names.distributionPoint||EMPTY_STRING,idBlock:{tagClass:3,tagNumber:0},value:[new Repeated({name:names.distributionPointNames||EMPTY_STRING,value:GeneralName.schema()})]}),new Constructed({name:names.distributionPoint||EMPTY_STRING,idBlock:{tagClass:3,tagNumber:1},value:RelativeDistinguishedNames.schema().valueBlock.value})]})]}),new Primitive({name:names.onlyContainsUserCerts||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:1}}),new Primitive({name:names.onlyContainsCACerts||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:2}}),new Primitive({name:names.onlySomeReasons||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:3}}),new Primitive({name:names.indirectCRL||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:4}}),new Primitive({name:names.onlyContainsAttributeCerts||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:5}})]});};var _proto23=IssuingDistributionPoint.prototype;_proto23.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1i);var asn1=compareSchema(schema,schema,IssuingDistributionPoint.schema({names:{distributionPoint:DISTRIBUTION_POINT,distributionPointNames:DISTRIBUTION_POINT_NAMES,onlyContainsUserCerts:ONLY_CONTAINS_USER_CERTS,onlyContainsCACerts:ONLY_CONTAINS_CA_CERTS,onlySomeReasons:ONLY_SOME_REASON,indirectCRL:INDIRECT_CRL,onlyContainsAttributeCerts:ONLY_CONTAINS_ATTRIBUTE_CERTS}}));AsnError.assertSchema(asn1,this.className);if(DISTRIBUTION_POINT in asn1.result){switch(true){case asn1.result.distributionPoint.idBlock.tagNumber===0:this.distributionPoint=Array.from(asn1.result.distributionPointNames,element=>new GeneralName({schema:element}));break;case asn1.result.distributionPoint.idBlock.tagNumber===1:{this.distributionPoint=new RelativeDistinguishedNames({schema:new Sequence({value:asn1.result.distributionPoint.valueBlock.value})});}break;default:throw new Error("Unknown tagNumber for distributionPoint: {$asn1.result.distributionPoint.idBlock.tagNumber}");}}if(ONLY_CONTAINS_USER_CERTS in asn1.result){var view=new Uint8Array(asn1.result.onlyContainsUserCerts.valueBlock.valueHex);this.onlyContainsUserCerts=view[0]!==0x00;}if(ONLY_CONTAINS_CA_CERTS in asn1.result){var _view2=new Uint8Array(asn1.result.onlyContainsCACerts.valueBlock.valueHex);this.onlyContainsCACerts=_view2[0]!==0x00;}if(ONLY_SOME_REASON in asn1.result){var _view3=new Uint8Array(asn1.result.onlySomeReasons.valueBlock.valueHex);this.onlySomeReasons=_view3[0];}if(INDIRECT_CRL in asn1.result){var _view4=new Uint8Array(asn1.result.indirectCRL.valueBlock.valueHex);this.indirectCRL=_view4[0]!==0x00;}if(ONLY_CONTAINS_ATTRIBUTE_CERTS in asn1.result){var _view5=new Uint8Array(asn1.result.onlyContainsAttributeCerts.valueBlock.valueHex);this.onlyContainsAttributeCerts=_view5[0]!==0x00;}};_proto23.toSchema=function toSchema(){var outputArray=[];if(this.distributionPoint){var value;if(this.distributionPoint instanceof Array){value=new Constructed({idBlock:{tagClass:3,tagNumber:0},value:Array.from(this.distributionPoint,o=>o.toSchema())});}else {value=this.distributionPoint.toSchema();value.idBlock.tagClass=3;value.idBlock.tagNumber=1;}outputArray.push(new Constructed({idBlock:{tagClass:3,tagNumber:0},value:[value]}));}if(this.onlyContainsUserCerts!==IssuingDistributionPoint.defaultValues(ONLY_CONTAINS_USER_CERTS)){outputArray.push(new Primitive({idBlock:{tagClass:3,tagNumber:1},valueHex:new Uint8Array([0xFF]).buffer}));}if(this.onlyContainsCACerts!==IssuingDistributionPoint.defaultValues(ONLY_CONTAINS_CA_CERTS)){outputArray.push(new Primitive({idBlock:{tagClass:3,tagNumber:2},valueHex:new Uint8Array([0xFF]).buffer}));}if(this.onlySomeReasons!==undefined){var buffer=new ArrayBuffer(1);var view=new Uint8Array(buffer);view[0]=this.onlySomeReasons;outputArray.push(new Primitive({idBlock:{tagClass:3,tagNumber:3},valueHex:buffer}));}if(this.indirectCRL!==IssuingDistributionPoint.defaultValues(INDIRECT_CRL)){outputArray.push(new Primitive({idBlock:{tagClass:3,tagNumber:4},valueHex:new Uint8Array([0xFF]).buffer}));}if(this.onlyContainsAttributeCerts!==IssuingDistributionPoint.defaultValues(ONLY_CONTAINS_ATTRIBUTE_CERTS)){outputArray.push(new Primitive({idBlock:{tagClass:3,tagNumber:5},valueHex:new Uint8Array([0xFF]).buffer}));}return new Sequence({value:outputArray});};_proto23.toJSON=function toJSON(){var obj={};if(this.distributionPoint){if(this.distributionPoint instanceof Array){obj.distributionPoint=Array.from(this.distributionPoint,o=>o.toJSON());}else {obj.distributionPoint=this.distributionPoint.toJSON();}}if(this.onlyContainsUserCerts!==IssuingDistributionPoint.defaultValues(ONLY_CONTAINS_USER_CERTS)){obj.onlyContainsUserCerts=this.onlyContainsUserCerts;}if(this.onlyContainsCACerts!==IssuingDistributionPoint.defaultValues(ONLY_CONTAINS_CA_CERTS)){obj.onlyContainsCACerts=this.onlyContainsCACerts;}if(ONLY_SOME_REASON in this){obj.onlySomeReasons=this.onlySomeReasons;}if(this.indirectCRL!==IssuingDistributionPoint.defaultValues(INDIRECT_CRL)){obj.indirectCRL=this.indirectCRL;}if(this.onlyContainsAttributeCerts!==IssuingDistributionPoint.defaultValues(ONLY_CONTAINS_ATTRIBUTE_CERTS)){obj.onlyContainsAttributeCerts=this.onlyContainsAttributeCerts;}return obj;};return IssuingDistributionPoint;}(PkiObject);IssuingDistributionPoint.CLASS_NAME="IssuingDistributionPoint";var BASE="base";var MINIMUM="minimum";var MAXIMUM="maximum";var CLEAR_PROPS$1h=[BASE,MINIMUM,MAXIMUM];var GeneralSubtree=/*#__PURE__*/function(_PkiObject23){_inheritsLoose(GeneralSubtree,_PkiObject23);function GeneralSubtree(parameters){var _this26;if(parameters===void 0){parameters={};}_this26=_PkiObject23.call(this)||this;_this26.base=getParametersValue(parameters,BASE,GeneralSubtree.defaultValues(BASE));_this26.minimum=getParametersValue(parameters,MINIMUM,GeneralSubtree.defaultValues(MINIMUM));if(MAXIMUM in parameters){_this26.maximum=getParametersValue(parameters,MAXIMUM,GeneralSubtree.defaultValues(MAXIMUM));}if(parameters.schema){_this26.fromSchema(parameters.schema);}return _this26;}GeneralSubtree.defaultValues=function defaultValues(memberName){switch(memberName){case BASE:return new GeneralName();case MINIMUM:return 0;case MAXIMUM:return 0;default:return _PkiObject23.defaultValues.call(this,memberName);}};GeneralSubtree.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[GeneralName.schema(names.base||{}),new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:0},value:[new Integer({name:names.minimum||EMPTY_STRING})]}),new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:1},value:[new Integer({name:names.maximum||EMPTY_STRING})]})]});};var _proto24=GeneralSubtree.prototype;_proto24.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1h);var asn1=compareSchema(schema,schema,GeneralSubtree.schema({names:{base:{names:{blockName:BASE}},minimum:MINIMUM,maximum:MAXIMUM}}));AsnError.assertSchema(asn1,this.className);this.base=new GeneralName({schema:asn1.result.base});if(MINIMUM in asn1.result){if(asn1.result.minimum.valueBlock.isHexOnly)this.minimum=asn1.result.minimum;else this.minimum=asn1.result.minimum.valueBlock.valueDec;}if(MAXIMUM in asn1.result){if(asn1.result.maximum.valueBlock.isHexOnly)this.maximum=asn1.result.maximum;else this.maximum=asn1.result.maximum.valueBlock.valueDec;}};_proto24.toSchema=function toSchema(){var outputArray=[];outputArray.push(this.base.toSchema());if(this.minimum!==0){var valueMinimum=0;if(this.minimum instanceof Integer){valueMinimum=this.minimum;}else {valueMinimum=new Integer({value:this.minimum});}outputArray.push(new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:0},value:[valueMinimum]}));}if(MAXIMUM in this){var valueMaximum=0;if(this.maximum instanceof Integer){valueMaximum=this.maximum;}else {valueMaximum=new Integer({value:this.maximum});}outputArray.push(new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:1},value:[valueMaximum]}));}return new Sequence({value:outputArray});};_proto24.toJSON=function toJSON(){var res={base:this.base.toJSON()};if(this.minimum!==0){if(typeof this.minimum==="number"){res.minimum=this.minimum;}else {res.minimum=this.minimum.toJSON();}}if(this.maximum!==undefined){if(typeof this.maximum==="number"){res.maximum=this.maximum;}else {res.maximum=this.maximum.toJSON();}}return res;};return GeneralSubtree;}(PkiObject);GeneralSubtree.CLASS_NAME="GeneralSubtree";var PERMITTED_SUBTREES="permittedSubtrees";var EXCLUDED_SUBTREES="excludedSubtrees";var CLEAR_PROPS$1g=[PERMITTED_SUBTREES,EXCLUDED_SUBTREES];var NameConstraints=/*#__PURE__*/function(_PkiObject24){_inheritsLoose(NameConstraints,_PkiObject24);function NameConstraints(parameters){var _this27;if(parameters===void 0){parameters={};}_this27=_PkiObject24.call(this)||this;if(PERMITTED_SUBTREES in parameters){_this27.permittedSubtrees=getParametersValue(parameters,PERMITTED_SUBTREES,NameConstraints.defaultValues(PERMITTED_SUBTREES));}if(EXCLUDED_SUBTREES in parameters){_this27.excludedSubtrees=getParametersValue(parameters,EXCLUDED_SUBTREES,NameConstraints.defaultValues(EXCLUDED_SUBTREES));}if(parameters.schema){_this27.fromSchema(parameters.schema);}return _this27;}NameConstraints.defaultValues=function defaultValues(memberName){switch(memberName){case PERMITTED_SUBTREES:case EXCLUDED_SUBTREES:return [];default:return _PkiObject24.defaultValues.call(this,memberName);}};NameConstraints.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:0},value:[new Repeated({name:names.permittedSubtrees||EMPTY_STRING,value:GeneralSubtree.schema()})]}),new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:1},value:[new Repeated({name:names.excludedSubtrees||EMPTY_STRING,value:GeneralSubtree.schema()})]})]});};var _proto25=NameConstraints.prototype;_proto25.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1g);var asn1=compareSchema(schema,schema,NameConstraints.schema({names:{permittedSubtrees:PERMITTED_SUBTREES,excludedSubtrees:EXCLUDED_SUBTREES}}));AsnError.assertSchema(asn1,this.className);if(PERMITTED_SUBTREES in asn1.result)this.permittedSubtrees=Array.from(asn1.result.permittedSubtrees,element=>new GeneralSubtree({schema:element}));if(EXCLUDED_SUBTREES in asn1.result)this.excludedSubtrees=Array.from(asn1.result.excludedSubtrees,element=>new GeneralSubtree({schema:element}));};_proto25.toSchema=function toSchema(){var outputArray=[];if(this.permittedSubtrees){outputArray.push(new Constructed({idBlock:{tagClass:3,tagNumber:0},value:Array.from(this.permittedSubtrees,o=>o.toSchema())}));}if(this.excludedSubtrees){outputArray.push(new Constructed({idBlock:{tagClass:3,tagNumber:1},value:Array.from(this.excludedSubtrees,o=>o.toSchema())}));}return new Sequence({value:outputArray});};_proto25.toJSON=function toJSON(){var object={};if(this.permittedSubtrees){object.permittedSubtrees=Array.from(this.permittedSubtrees,o=>o.toJSON());}if(this.excludedSubtrees){object.excludedSubtrees=Array.from(this.excludedSubtrees,o=>o.toJSON());}return object;};return NameConstraints;}(PkiObject);NameConstraints.CLASS_NAME="NameConstraints";var REQUIRE_EXPLICIT_POLICY="requireExplicitPolicy";var INHIBIT_POLICY_MAPPING="inhibitPolicyMapping";var CLEAR_PROPS$1f=[REQUIRE_EXPLICIT_POLICY,INHIBIT_POLICY_MAPPING];var PolicyConstraints=/*#__PURE__*/function(_PkiObject25){_inheritsLoose(PolicyConstraints,_PkiObject25);function PolicyConstraints(parameters){var _this28;if(parameters===void 0){parameters={};}_this28=_PkiObject25.call(this)||this;if(REQUIRE_EXPLICIT_POLICY in parameters){_this28.requireExplicitPolicy=getParametersValue(parameters,REQUIRE_EXPLICIT_POLICY,PolicyConstraints.defaultValues(REQUIRE_EXPLICIT_POLICY));}if(INHIBIT_POLICY_MAPPING in parameters){_this28.inhibitPolicyMapping=getParametersValue(parameters,INHIBIT_POLICY_MAPPING,PolicyConstraints.defaultValues(INHIBIT_POLICY_MAPPING));}if(parameters.schema){_this28.fromSchema(parameters.schema);}return _this28;}PolicyConstraints.defaultValues=function defaultValues(memberName){switch(memberName){case REQUIRE_EXPLICIT_POLICY:return 0;case INHIBIT_POLICY_MAPPING:return 0;default:return _PkiObject25.defaultValues.call(this,memberName);}};PolicyConstraints.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Primitive({name:names.requireExplicitPolicy||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:0}}),new Primitive({name:names.inhibitPolicyMapping||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:1}})]});};var _proto26=PolicyConstraints.prototype;_proto26.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1f);var asn1=compareSchema(schema,schema,PolicyConstraints.schema({names:{requireExplicitPolicy:REQUIRE_EXPLICIT_POLICY,inhibitPolicyMapping:INHIBIT_POLICY_MAPPING}}));AsnError.assertSchema(asn1,this.className);if(REQUIRE_EXPLICIT_POLICY in asn1.result){var field1=asn1.result.requireExplicitPolicy;field1.idBlock.tagClass=1;field1.idBlock.tagNumber=2;var ber1=field1.toBER(false);var int1=fromBER(ber1);AsnError.assert(int1,"Integer");this.requireExplicitPolicy=int1.result.valueBlock.valueDec;}if(INHIBIT_POLICY_MAPPING in asn1.result){var field2=asn1.result.inhibitPolicyMapping;field2.idBlock.tagClass=1;field2.idBlock.tagNumber=2;var ber2=field2.toBER(false);var int2=fromBER(ber2);AsnError.assert(int2,"Integer");this.inhibitPolicyMapping=int2.result.valueBlock.valueDec;}};_proto26.toSchema=function toSchema(){var outputArray=[];if(REQUIRE_EXPLICIT_POLICY in this){var int1=new Integer({value:this.requireExplicitPolicy});int1.idBlock.tagClass=3;int1.idBlock.tagNumber=0;outputArray.push(int1);}if(INHIBIT_POLICY_MAPPING in this){var int2=new Integer({value:this.inhibitPolicyMapping});int2.idBlock.tagClass=3;int2.idBlock.tagNumber=1;outputArray.push(int2);}return new Sequence({value:outputArray});};_proto26.toJSON=function toJSON(){var res={};if(REQUIRE_EXPLICIT_POLICY in this){res.requireExplicitPolicy=this.requireExplicitPolicy;}if(INHIBIT_POLICY_MAPPING in this){res.inhibitPolicyMapping=this.inhibitPolicyMapping;}return res;};return PolicyConstraints;}(PkiObject);PolicyConstraints.CLASS_NAME="PolicyConstraints";var ISSUER_DOMAIN_POLICY="issuerDomainPolicy";var SUBJECT_DOMAIN_POLICY="subjectDomainPolicy";var CLEAR_PROPS$1e=[ISSUER_DOMAIN_POLICY,SUBJECT_DOMAIN_POLICY];var PolicyMapping=/*#__PURE__*/function(_PkiObject26){_inheritsLoose(PolicyMapping,_PkiObject26);function PolicyMapping(parameters){var _this29;if(parameters===void 0){parameters={};}_this29=_PkiObject26.call(this)||this;_this29.issuerDomainPolicy=getParametersValue(parameters,ISSUER_DOMAIN_POLICY,PolicyMapping.defaultValues(ISSUER_DOMAIN_POLICY));_this29.subjectDomainPolicy=getParametersValue(parameters,SUBJECT_DOMAIN_POLICY,PolicyMapping.defaultValues(SUBJECT_DOMAIN_POLICY));if(parameters.schema){_this29.fromSchema(parameters.schema);}return _this29;}PolicyMapping.defaultValues=function defaultValues(memberName){switch(memberName){case ISSUER_DOMAIN_POLICY:return EMPTY_STRING;case SUBJECT_DOMAIN_POLICY:return EMPTY_STRING;default:return _PkiObject26.defaultValues.call(this,memberName);}};PolicyMapping.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new ObjectIdentifier({name:names.issuerDomainPolicy||EMPTY_STRING}),new ObjectIdentifier({name:names.subjectDomainPolicy||EMPTY_STRING})]});};var _proto27=PolicyMapping.prototype;_proto27.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1e);var asn1=compareSchema(schema,schema,PolicyMapping.schema({names:{issuerDomainPolicy:ISSUER_DOMAIN_POLICY,subjectDomainPolicy:SUBJECT_DOMAIN_POLICY}}));AsnError.assertSchema(asn1,this.className);this.issuerDomainPolicy=asn1.result.issuerDomainPolicy.valueBlock.toString();this.subjectDomainPolicy=asn1.result.subjectDomainPolicy.valueBlock.toString();};_proto27.toSchema=function toSchema(){return new Sequence({value:[new ObjectIdentifier({value:this.issuerDomainPolicy}),new ObjectIdentifier({value:this.subjectDomainPolicy})]});};_proto27.toJSON=function toJSON(){return {issuerDomainPolicy:this.issuerDomainPolicy,subjectDomainPolicy:this.subjectDomainPolicy};};return PolicyMapping;}(PkiObject);PolicyMapping.CLASS_NAME="PolicyMapping";var MAPPINGS="mappings";var CLEAR_PROPS$1d=[MAPPINGS];var PolicyMappings=/*#__PURE__*/function(_PkiObject27){_inheritsLoose(PolicyMappings,_PkiObject27);function PolicyMappings(parameters){var _this30;if(parameters===void 0){parameters={};}_this30=_PkiObject27.call(this)||this;_this30.mappings=getParametersValue(parameters,MAPPINGS,PolicyMappings.defaultValues(MAPPINGS));if(parameters.schema){_this30.fromSchema(parameters.schema);}return _this30;}PolicyMappings.defaultValues=function defaultValues(memberName){switch(memberName){case MAPPINGS:return [];default:return _PkiObject27.defaultValues.call(this,memberName);}};PolicyMappings.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Repeated({name:names.mappings||EMPTY_STRING,value:PolicyMapping.schema()})]});};var _proto28=PolicyMappings.prototype;_proto28.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1d);var asn1=compareSchema(schema,schema,PolicyMappings.schema({names:{mappings:MAPPINGS}}));AsnError.assertSchema(asn1,this.className);this.mappings=Array.from(asn1.result.mappings,element=>new PolicyMapping({schema:element}));};_proto28.toSchema=function toSchema(){return new Sequence({value:Array.from(this.mappings,o=>o.toSchema())});};_proto28.toJSON=function toJSON(){return {mappings:Array.from(this.mappings,o=>o.toJSON())};};return PolicyMappings;}(PkiObject);PolicyMappings.CLASS_NAME="PolicyMappings";var NOT_BEFORE$1="notBefore";var NOT_AFTER$1="notAfter";var CLEAR_PROPS$1c=[NOT_BEFORE$1,NOT_AFTER$1];var PrivateKeyUsagePeriod=/*#__PURE__*/function(_PkiObject28){_inheritsLoose(PrivateKeyUsagePeriod,_PkiObject28);function PrivateKeyUsagePeriod(parameters){var _this31;if(parameters===void 0){parameters={};}_this31=_PkiObject28.call(this)||this;if(NOT_BEFORE$1 in parameters){_this31.notBefore=getParametersValue(parameters,NOT_BEFORE$1,PrivateKeyUsagePeriod.defaultValues(NOT_BEFORE$1));}if(NOT_AFTER$1 in parameters){_this31.notAfter=getParametersValue(parameters,NOT_AFTER$1,PrivateKeyUsagePeriod.defaultValues(NOT_AFTER$1));}if(parameters.schema){_this31.fromSchema(parameters.schema);}return _this31;}PrivateKeyUsagePeriod.defaultValues=function defaultValues(memberName){switch(memberName){case NOT_BEFORE$1:return new Date();case NOT_AFTER$1:return new Date();default:return _PkiObject28.defaultValues.call(this,memberName);}};PrivateKeyUsagePeriod.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Primitive({name:names.notBefore||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:0}}),new Primitive({name:names.notAfter||EMPTY_STRING,optional:true,idBlock:{tagClass:3,tagNumber:1}})]});};var _proto29=PrivateKeyUsagePeriod.prototype;_proto29.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1c);var asn1=compareSchema(schema,schema,PrivateKeyUsagePeriod.schema({names:{notBefore:NOT_BEFORE$1,notAfter:NOT_AFTER$1}}));AsnError.assertSchema(asn1,this.className);if(NOT_BEFORE$1 in asn1.result){var localNotBefore=new GeneralizedTime();localNotBefore.fromBuffer(asn1.result.notBefore.valueBlock.valueHex);this.notBefore=localNotBefore.toDate();}if(NOT_AFTER$1 in asn1.result){var localNotAfter=new GeneralizedTime({valueHex:asn1.result.notAfter.valueBlock.valueHex});localNotAfter.fromBuffer(asn1.result.notAfter.valueBlock.valueHex);this.notAfter=localNotAfter.toDate();}};_proto29.toSchema=function toSchema(){var outputArray=[];if(NOT_BEFORE$1 in this){outputArray.push(new Primitive({idBlock:{tagClass:3,tagNumber:0},valueHex:new GeneralizedTime({valueDate:this.notBefore}).valueBlock.valueHexView}));}if(NOT_AFTER$1 in this){outputArray.push(new Primitive({idBlock:{tagClass:3,tagNumber:1},valueHex:new GeneralizedTime({valueDate:this.notAfter}).valueBlock.valueHexView}));}return new Sequence({value:outputArray});};_proto29.toJSON=function toJSON(){var res={};if(this.notBefore){res.notBefore=this.notBefore;}if(this.notAfter){res.notAfter=this.notAfter;}return res;};return PrivateKeyUsagePeriod;}(PkiObject);PrivateKeyUsagePeriod.CLASS_NAME="PrivateKeyUsagePeriod";var ID="id";var TYPE$2="type";var VALUES="values";var QC_STATEMENT_CLEAR_PROPS=[ID,TYPE$2];var QC_STATEMENTS_CLEAR_PROPS=[VALUES];var QCStatement=/*#__PURE__*/function(_PkiObject29){_inheritsLoose(QCStatement,_PkiObject29);function QCStatement(parameters){var _this32;if(parameters===void 0){parameters={};}_this32=_PkiObject29.call(this)||this;_this32.id=getParametersValue(parameters,ID,QCStatement.defaultValues(ID));if(TYPE$2 in parameters){_this32.type=getParametersValue(parameters,TYPE$2,QCStatement.defaultValues(TYPE$2));}if(parameters.schema){_this32.fromSchema(parameters.schema);}return _this32;}QCStatement.defaultValues=function defaultValues(memberName){switch(memberName){case ID:return EMPTY_STRING;case TYPE$2:return new Null();default:return _PkiObject29.defaultValues.call(this,memberName);}};QCStatement.compareWithDefault=function compareWithDefault(memberName,memberValue){switch(memberName){case ID:return memberValue===EMPTY_STRING;case TYPE$2:return memberValue instanceof Null;default:return _PkiObject29.defaultValues.call(this,memberName);}};QCStatement.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new ObjectIdentifier({name:names.id||EMPTY_STRING}),new Any({name:names.type||EMPTY_STRING,optional:true})]});};var _proto30=QCStatement.prototype;_proto30.fromSchema=function fromSchema(schema){clearProps(schema,QC_STATEMENT_CLEAR_PROPS);var asn1=compareSchema(schema,schema,QCStatement.schema({names:{id:ID,type:TYPE$2}}));AsnError.assertSchema(asn1,this.className);this.id=asn1.result.id.valueBlock.toString();if(TYPE$2 in asn1.result)this.type=asn1.result.type;};_proto30.toSchema=function toSchema(){var value=[new ObjectIdentifier({value:this.id})];if(TYPE$2 in this)value.push(this.type);return new Sequence({value});};_proto30.toJSON=function toJSON(){var object={id:this.id};if(this.type){object.type=this.type.toJSON();}return object;};return QCStatement;}(PkiObject);QCStatement.CLASS_NAME="QCStatement";var QCStatements=/*#__PURE__*/function(_PkiObject30){_inheritsLoose(QCStatements,_PkiObject30);function QCStatements(parameters){var _this33;if(parameters===void 0){parameters={};}_this33=_PkiObject30.call(this)||this;_this33.values=getParametersValue(parameters,VALUES,QCStatements.defaultValues(VALUES));if(parameters.schema){_this33.fromSchema(parameters.schema);}return _this33;}QCStatements.defaultValues=function defaultValues(memberName){switch(memberName){case VALUES:return [];default:return _PkiObject30.defaultValues.call(this,memberName);}};QCStatements.compareWithDefault=function compareWithDefault(memberName,memberValue){switch(memberName){case VALUES:return memberValue.length===0;default:return _PkiObject30.defaultValues.call(this,memberName);}};QCStatements.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Repeated({name:names.values||EMPTY_STRING,value:QCStatement.schema(names.value||{})})]});};var _proto31=QCStatements.prototype;_proto31.fromSchema=function fromSchema(schema){clearProps(schema,QC_STATEMENTS_CLEAR_PROPS);var asn1=compareSchema(schema,schema,QCStatements.schema({names:{values:VALUES}}));AsnError.assertSchema(asn1,this.className);this.values=Array.from(asn1.result.values,element=>new QCStatement({schema:element}));};_proto31.toSchema=function toSchema(){return new Sequence({value:Array.from(this.values,o=>o.toSchema())});};_proto31.toJSON=function toJSON(){return {values:Array.from(this.values,o=>o.toJSON())};};return QCStatements;}(PkiObject);QCStatements.CLASS_NAME="QCStatements";var _a;var ECNamedCurves=/*#__PURE__*/function(){function ECNamedCurves(){}ECNamedCurves.register=function register(name,id,size){this.namedCurves[name.toLowerCase()]=this.namedCurves[id]={name,id,size};};ECNamedCurves.find=function find(nameOrId){return this.namedCurves[nameOrId.toLowerCase()]||null;};return ECNamedCurves;}();_a=ECNamedCurves;ECNamedCurves.namedCurves={};(()=>{_a.register("P-256","1.2.840.10045.3.1.7",32);_a.register("P-384","1.3.132.0.34",48);_a.register("P-521","1.3.132.0.35",66);_a.register("brainpoolP256r1","1.3.36.3.3.2.8.1.1.7",32);_a.register("brainpoolP384r1","1.3.36.3.3.2.8.1.1.11",48);_a.register("brainpoolP512r1","1.3.36.3.3.2.8.1.1.13",64);})();var X="x";var Y="y";var NAMED_CURVE$1="namedCurve";var ECPublicKey=/*#__PURE__*/function(_PkiObject31){_inheritsLoose(ECPublicKey,_PkiObject31);function ECPublicKey(parameters){var _this34;if(parameters===void 0){parameters={};}_this34=_PkiObject31.call(this)||this;_this34.x=getParametersValue(parameters,X,ECPublicKey.defaultValues(X));_this34.y=getParametersValue(parameters,Y,ECPublicKey.defaultValues(Y));_this34.namedCurve=getParametersValue(parameters,NAMED_CURVE$1,ECPublicKey.defaultValues(NAMED_CURVE$1));if(parameters.json){_this34.fromJSON(parameters.json);}if(parameters.schema){_this34.fromSchema(parameters.schema);}return _this34;}ECPublicKey.defaultValues=function defaultValues(memberName){switch(memberName){case X:case Y:return EMPTY_BUFFER;case NAMED_CURVE$1:return EMPTY_STRING;default:return _PkiObject31.defaultValues.call(this,memberName);}};ECPublicKey.compareWithDefault=function compareWithDefault(memberName,memberValue){switch(memberName){case X:case Y:return memberValue instanceof ArrayBuffer&&isEqualBuffer(memberValue,ECPublicKey.defaultValues(memberName));case NAMED_CURVE$1:return typeof memberValue==="string"&&memberValue===ECPublicKey.defaultValues(memberName);default:return _PkiObject31.defaultValues.call(this,memberName);}};ECPublicKey.schema=function schema(){return new RawData();};var _proto32=ECPublicKey.prototype;_proto32.fromSchema=function fromSchema(schema1){var view=BufferSourceConverter.toUint8Array(schema1);if(view[0]!==0x04){throw new Error("Object's schema was not verified against input data for ECPublicKey");}var namedCurve=ECNamedCurves.find(this.namedCurve);if(!namedCurve){throw new Error(`Incorrect curve OID: ${this.namedCurve}`);}var coordinateLength=namedCurve.size;if(view.byteLength!==coordinateLength*2+1){throw new Error("Object's schema was not verified against input data for ECPublicKey");}this.namedCurve=namedCurve.name;this.x=view.slice(1,coordinateLength+1).buffer;this.y=view.slice(1+coordinateLength,coordinateLength*2+1).buffer;};_proto32.toSchema=function toSchema(){return new RawData({data:utilConcatBuf(new Uint8Array([0x04]).buffer,this.x,this.y)});};_proto32.toJSON=function toJSON(){var namedCurve=ECNamedCurves.find(this.namedCurve);return {crv:namedCurve?namedCurve.name:this.namedCurve,x:toBase64(arrayBufferToString(this.x),true,true,false),y:toBase64(arrayBufferToString(this.y),true,true,false)};};_proto32.fromJSON=function fromJSON(json){ParameterError.assert("json",json,"crv","x","y");var coordinateLength=0;var namedCurve=ECNamedCurves.find(json.crv);if(namedCurve){this.namedCurve=namedCurve.id;coordinateLength=namedCurve.size;}var xConvertBuffer=stringToArrayBuffer(fromBase64(json.x,true));if(xConvertBuffer.byteLength<coordinateLength){this.x=new ArrayBuffer(coordinateLength);var view=new Uint8Array(this.x);var convertBufferView=new Uint8Array(xConvertBuffer);view.set(convertBufferView,1);}else {this.x=xConvertBuffer.slice(0,coordinateLength);}var yConvertBuffer=stringToArrayBuffer(fromBase64(json.y,true));if(yConvertBuffer.byteLength<coordinateLength){this.y=new ArrayBuffer(coordinateLength);var _view6=new Uint8Array(this.y);var _convertBufferView=new Uint8Array(yConvertBuffer);_view6.set(_convertBufferView,1);}else {this.y=yConvertBuffer.slice(0,coordinateLength);}};return ECPublicKey;}(PkiObject);ECPublicKey.CLASS_NAME="ECPublicKey";var MODULUS$1="modulus";var PUBLIC_EXPONENT$1="publicExponent";var CLEAR_PROPS$1b=[MODULUS$1,PUBLIC_EXPONENT$1];var RSAPublicKey=/*#__PURE__*/function(_PkiObject32){_inheritsLoose(RSAPublicKey,_PkiObject32);function RSAPublicKey(parameters){var _this35;if(parameters===void 0){parameters={};}_this35=_PkiObject32.call(this)||this;_this35.modulus=getParametersValue(parameters,MODULUS$1,RSAPublicKey.defaultValues(MODULUS$1));_this35.publicExponent=getParametersValue(parameters,PUBLIC_EXPONENT$1,RSAPublicKey.defaultValues(PUBLIC_EXPONENT$1));if(parameters.json){_this35.fromJSON(parameters.json);}if(parameters.schema){_this35.fromSchema(parameters.schema);}return _this35;}RSAPublicKey.defaultValues=function defaultValues(memberName){switch(memberName){case MODULUS$1:return new Integer();case PUBLIC_EXPONENT$1:return new Integer();default:return _PkiObject32.defaultValues.call(this,memberName);}};RSAPublicKey.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Integer({name:names.modulus||EMPTY_STRING}),new Integer({name:names.publicExponent||EMPTY_STRING})]});};var _proto33=RSAPublicKey.prototype;_proto33.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1b);var asn1=compareSchema(schema,schema,RSAPublicKey.schema({names:{modulus:MODULUS$1,publicExponent:PUBLIC_EXPONENT$1}}));AsnError.assertSchema(asn1,this.className);this.modulus=asn1.result.modulus.convertFromDER(256);this.publicExponent=asn1.result.publicExponent;};_proto33.toSchema=function toSchema(){return new Sequence({value:[this.modulus.convertToDER(),this.publicExponent]});};_proto33.toJSON=function toJSON(){return {n:Convert.ToBase64Url(this.modulus.valueBlock.valueHexView),e:Convert.ToBase64Url(this.publicExponent.valueBlock.valueHexView)};};_proto33.fromJSON=function fromJSON(json){ParameterError.assert("json",json,"n","e");var array=stringToArrayBuffer(fromBase64(json.n,true));this.modulus=new Integer({valueHex:array.slice(0,Math.pow(2,nearestPowerOf2(array.byteLength)))});this.publicExponent=new Integer({valueHex:stringToArrayBuffer(fromBase64(json.e,true)).slice(0,3)});};return RSAPublicKey;}(PkiObject);RSAPublicKey.CLASS_NAME="RSAPublicKey";var ALGORITHM$1="algorithm";var SUBJECT_PUBLIC_KEY="subjectPublicKey";var CLEAR_PROPS$1a=[ALGORITHM$1,SUBJECT_PUBLIC_KEY];var PublicKeyInfo=/*#__PURE__*/function(_PkiObject33){_inheritsLoose(PublicKeyInfo,_PkiObject33);function PublicKeyInfo(parameters){var _this36;if(parameters===void 0){parameters={};}_this36=_PkiObject33.call(this)||this;_this36.algorithm=getParametersValue(parameters,ALGORITHM$1,PublicKeyInfo.defaultValues(ALGORITHM$1));_this36.subjectPublicKey=getParametersValue(parameters,SUBJECT_PUBLIC_KEY,PublicKeyInfo.defaultValues(SUBJECT_PUBLIC_KEY));var parsedKey=getParametersValue(parameters,"parsedKey",null);if(parsedKey){_this36.parsedKey=parsedKey;}if(parameters.json){_this36.fromJSON(parameters.json);}if(parameters.schema){_this36.fromSchema(parameters.schema);}return _this36;}PublicKeyInfo.defaultValues=function defaultValues(memberName){switch(memberName){case ALGORITHM$1:return new AlgorithmIdentifier();case SUBJECT_PUBLIC_KEY:return new BitString();default:return _PkiObject33.defaultValues.call(this,memberName);}};PublicKeyInfo.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[AlgorithmIdentifier.schema(names.algorithm||{}),new BitString({name:names.subjectPublicKey||EMPTY_STRING})]});};var _proto34=PublicKeyInfo.prototype;_proto34.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$1a);var asn1=compareSchema(schema,schema,PublicKeyInfo.schema({names:{algorithm:{names:{blockName:ALGORITHM$1}},subjectPublicKey:SUBJECT_PUBLIC_KEY}}));AsnError.assertSchema(asn1,this.className);this.algorithm=new AlgorithmIdentifier({schema:asn1.result.algorithm});this.subjectPublicKey=asn1.result.subjectPublicKey;};_proto34.toSchema=function toSchema(){return new Sequence({value:[this.algorithm.toSchema(),this.subjectPublicKey]});};_proto34.toJSON=function toJSON(){if(!this.parsedKey){return {algorithm:this.algorithm.toJSON(),subjectPublicKey:this.subjectPublicKey.toJSON()};}var jwk={};switch(this.algorithm.algorithmId){case"1.2.840.10045.2.1":jwk.kty="EC";break;case"1.2.840.113549.1.1.1":jwk.kty="RSA";break;}var publicKeyJWK=this.parsedKey.toJSON();Object.assign(jwk,publicKeyJWK);return jwk;};_proto34.fromJSON=function fromJSON(json){if("kty"in json){switch(json.kty.toUpperCase()){case"EC":this.parsedKey=new ECPublicKey({json});this.algorithm=new AlgorithmIdentifier({algorithmId:"1.2.840.10045.2.1",algorithmParams:new ObjectIdentifier({value:this.parsedKey.namedCurve})});break;case"RSA":this.parsedKey=new RSAPublicKey({json});this.algorithm=new AlgorithmIdentifier({algorithmId:"1.2.840.113549.1.1.1",algorithmParams:new Null()});break;default:throw new Error(`Invalid value for "kty" parameter: ${json.kty}`);}this.subjectPublicKey=new BitString({valueHex:this.parsedKey.toSchema().toBER(false)});}};_proto34.importKey=function importKey(publicKey,crypto){try{var _this37=this;if(crypto===void 0){crypto=getCrypto(true);}return _await(_catch(()=>{if(!publicKey){throw new Error("Need to provide publicKey input parameter");}return _await(crypto.exportKey("spki",publicKey),exportedKey=>{var asn1=fromBER(exportedKey);try{_this37.fromSchema(asn1.result);}catch(exception){throw new Error("Error during initializing object from schema");}});},e=>{var message=e instanceof Error?e.message:`${e}`;throw new Error(`Error during exporting public key: ${message}`);}));}catch(e){return Promise.reject(e);}};_createClass(PublicKeyInfo,[{key:"parsedKey",get:function(){if(this._parsedKey===undefined){switch(this.algorithm.algorithmId){case"1.2.840.10045.2.1":if("algorithmParams"in this.algorithm){if(this.algorithm.algorithmParams.constructor.blockName()===ObjectIdentifier.blockName()){try{this._parsedKey=new ECPublicKey({namedCurve:this.algorithm.algorithmParams.valueBlock.toString(),schema:this.subjectPublicKey.valueBlock.valueHexView});}catch(ex){}}}break;case"1.2.840.113549.1.1.1":{var publicKeyASN1=fromBER(this.subjectPublicKey.valueBlock.valueHexView);if(publicKeyASN1.offset!==-1){try{this._parsedKey=new RSAPublicKey({schema:publicKeyASN1.result});}catch(ex){}}}break;}this._parsedKey||(this._parsedKey=null);}return this._parsedKey||undefined;},set:function(value){this._parsedKey=value;}}]);return PublicKeyInfo;}(PkiObject);PublicKeyInfo.CLASS_NAME="PublicKeyInfo";var VERSION$l="version";var PRIVATE_KEY$1="privateKey";var NAMED_CURVE="namedCurve";var PUBLIC_KEY$1="publicKey";var CLEAR_PROPS$19=[VERSION$l,PRIVATE_KEY$1,NAMED_CURVE,PUBLIC_KEY$1];var ECPrivateKey=/*#__PURE__*/function(_PkiObject34){_inheritsLoose(ECPrivateKey,_PkiObject34);function ECPrivateKey(parameters){var _this38;if(parameters===void 0){parameters={};}_this38=_PkiObject34.call(this)||this;_this38.version=getParametersValue(parameters,VERSION$l,ECPrivateKey.defaultValues(VERSION$l));_this38.privateKey=getParametersValue(parameters,PRIVATE_KEY$1,ECPrivateKey.defaultValues(PRIVATE_KEY$1));if(NAMED_CURVE in parameters){_this38.namedCurve=getParametersValue(parameters,NAMED_CURVE,ECPrivateKey.defaultValues(NAMED_CURVE));}if(PUBLIC_KEY$1 in parameters){_this38.publicKey=getParametersValue(parameters,PUBLIC_KEY$1,ECPrivateKey.defaultValues(PUBLIC_KEY$1));}if(parameters.json){_this38.fromJSON(parameters.json);}if(parameters.schema){_this38.fromSchema(parameters.schema);}return _this38;}ECPrivateKey.defaultValues=function defaultValues(memberName){switch(memberName){case VERSION$l:return 1;case PRIVATE_KEY$1:return new OctetString();case NAMED_CURVE:return EMPTY_STRING;case PUBLIC_KEY$1:return new ECPublicKey();default:return _PkiObject34.defaultValues.call(this,memberName);}};ECPrivateKey.compareWithDefault=function compareWithDefault(memberName,memberValue){switch(memberName){case VERSION$l:return memberValue===ECPrivateKey.defaultValues(memberName);case PRIVATE_KEY$1:return memberValue.isEqual(ECPrivateKey.defaultValues(memberName));case NAMED_CURVE:return memberValue===EMPTY_STRING;case PUBLIC_KEY$1:return ECPublicKey.compareWithDefault(NAMED_CURVE,memberValue.namedCurve)&&ECPublicKey.compareWithDefault("x",memberValue.x)&&ECPublicKey.compareWithDefault("y",memberValue.y);default:return _PkiObject34.defaultValues.call(this,memberName);}};ECPrivateKey.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Integer({name:names.version||EMPTY_STRING}),new OctetString({name:names.privateKey||EMPTY_STRING}),new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:0},value:[new ObjectIdentifier({name:names.namedCurve||EMPTY_STRING})]}),new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:1},value:[new BitString({name:names.publicKey||EMPTY_STRING})]})]});};var _proto35=ECPrivateKey.prototype;_proto35.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$19);var asn1=compareSchema(schema,schema,ECPrivateKey.schema({names:{version:VERSION$l,privateKey:PRIVATE_KEY$1,namedCurve:NAMED_CURVE,publicKey:PUBLIC_KEY$1}}));AsnError.assertSchema(asn1,this.className);this.version=asn1.result.version.valueBlock.valueDec;this.privateKey=asn1.result.privateKey;if(NAMED_CURVE in asn1.result){this.namedCurve=asn1.result.namedCurve.valueBlock.toString();}if(PUBLIC_KEY$1 in asn1.result){var publicKeyData={schema:asn1.result.publicKey.valueBlock.valueHex};if(NAMED_CURVE in this){publicKeyData.namedCurve=this.namedCurve;}this.publicKey=new ECPublicKey(publicKeyData);}};_proto35.toSchema=function toSchema(){var outputArray=[new Integer({value:this.version}),this.privateKey];if(this.namedCurve){outputArray.push(new Constructed({idBlock:{tagClass:3,tagNumber:0},value:[new ObjectIdentifier({value:this.namedCurve})]}));}if(this.publicKey){outputArray.push(new Constructed({idBlock:{tagClass:3,tagNumber:1},value:[new BitString({valueHex:this.publicKey.toSchema().toBER(false)})]}));}return new Sequence({value:outputArray});};_proto35.toJSON=function toJSON(){if(!this.namedCurve||ECPrivateKey.compareWithDefault(NAMED_CURVE,this.namedCurve)){throw new Error("Not enough information for making JSON: absent \"namedCurve\" value");}var curve=ECNamedCurves.find(this.namedCurve);var privateKeyJSON={crv:curve?curve.name:this.namedCurve,d:Convert.ToBase64Url(this.privateKey.valueBlock.valueHexView)};if(this.publicKey){var publicKeyJSON=this.publicKey.toJSON();privateKeyJSON.x=publicKeyJSON.x;privateKeyJSON.y=publicKeyJSON.y;}return privateKeyJSON;};_proto35.fromJSON=function fromJSON(json){ParameterError.assert("json",json,"crv","d");var coordinateLength=0;var curve=ECNamedCurves.find(json.crv);if(curve){this.namedCurve=curve.id;coordinateLength=curve.size;}var convertBuffer=Convert.FromBase64Url(json.d);if(convertBuffer.byteLength<coordinateLength){var buffer=new ArrayBuffer(coordinateLength);var view=new Uint8Array(buffer);var convertBufferView=new Uint8Array(convertBuffer);view.set(convertBufferView,1);this.privateKey=new OctetString({valueHex:buffer});}else {this.privateKey=new OctetString({valueHex:convertBuffer.slice(0,coordinateLength)});}if(json.x&&json.y){this.publicKey=new ECPublicKey({json});}};return ECPrivateKey;}(PkiObject);ECPrivateKey.CLASS_NAME="ECPrivateKey";var PRIME="prime";var EXPONENT="exponent";var COEFFICIENT$1="coefficient";var CLEAR_PROPS$18=[PRIME,EXPONENT,COEFFICIENT$1];var OtherPrimeInfo=/*#__PURE__*/function(_PkiObject35){_inheritsLoose(OtherPrimeInfo,_PkiObject35);function OtherPrimeInfo(parameters){var _this39;if(parameters===void 0){parameters={};}_this39=_PkiObject35.call(this)||this;_this39.prime=getParametersValue(parameters,PRIME,OtherPrimeInfo.defaultValues(PRIME));_this39.exponent=getParametersValue(parameters,EXPONENT,OtherPrimeInfo.defaultValues(EXPONENT));_this39.coefficient=getParametersValue(parameters,COEFFICIENT$1,OtherPrimeInfo.defaultValues(COEFFICIENT$1));if(parameters.json){_this39.fromJSON(parameters.json);}if(parameters.schema){_this39.fromSchema(parameters.schema);}return _this39;}OtherPrimeInfo.defaultValues=function defaultValues(memberName){switch(memberName){case PRIME:return new Integer();case EXPONENT:return new Integer();case COEFFICIENT$1:return new Integer();default:return _PkiObject35.defaultValues.call(this,memberName);}};OtherPrimeInfo.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Integer({name:names.prime||EMPTY_STRING}),new Integer({name:names.exponent||EMPTY_STRING}),new Integer({name:names.coefficient||EMPTY_STRING})]});};var _proto36=OtherPrimeInfo.prototype;_proto36.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$18);var asn1=compareSchema(schema,schema,OtherPrimeInfo.schema({names:{prime:PRIME,exponent:EXPONENT,coefficient:COEFFICIENT$1}}));AsnError.assertSchema(asn1,this.className);this.prime=asn1.result.prime.convertFromDER();this.exponent=asn1.result.exponent.convertFromDER();this.coefficient=asn1.result.coefficient.convertFromDER();};_proto36.toSchema=function toSchema(){return new Sequence({value:[this.prime.convertToDER(),this.exponent.convertToDER(),this.coefficient.convertToDER()]});};_proto36.toJSON=function toJSON(){return {r:Convert.ToBase64Url(this.prime.valueBlock.valueHexView),d:Convert.ToBase64Url(this.exponent.valueBlock.valueHexView),t:Convert.ToBase64Url(this.coefficient.valueBlock.valueHexView)};};_proto36.fromJSON=function fromJSON(json){ParameterError.assert("json",json,"r","d","r");this.prime=new Integer({valueHex:Convert.FromBase64Url(json.r)});this.exponent=new Integer({valueHex:Convert.FromBase64Url(json.d)});this.coefficient=new Integer({valueHex:Convert.FromBase64Url(json.t)});};return OtherPrimeInfo;}(PkiObject);OtherPrimeInfo.CLASS_NAME="OtherPrimeInfo";var VERSION$k="version";var MODULUS="modulus";var PUBLIC_EXPONENT="publicExponent";var PRIVATE_EXPONENT="privateExponent";var PRIME1="prime1";var PRIME2="prime2";var EXPONENT1="exponent1";var EXPONENT2="exponent2";var COEFFICIENT="coefficient";var OTHER_PRIME_INFOS="otherPrimeInfos";var CLEAR_PROPS$17=[VERSION$k,MODULUS,PUBLIC_EXPONENT,PRIVATE_EXPONENT,PRIME1,PRIME2,EXPONENT1,EXPONENT2,COEFFICIENT,OTHER_PRIME_INFOS];var RSAPrivateKey=/*#__PURE__*/function(_PkiObject36){_inheritsLoose(RSAPrivateKey,_PkiObject36);function RSAPrivateKey(parameters){var _this40;if(parameters===void 0){parameters={};}_this40=_PkiObject36.call(this)||this;_this40.version=getParametersValue(parameters,VERSION$k,RSAPrivateKey.defaultValues(VERSION$k));_this40.modulus=getParametersValue(parameters,MODULUS,RSAPrivateKey.defaultValues(MODULUS));_this40.publicExponent=getParametersValue(parameters,PUBLIC_EXPONENT,RSAPrivateKey.defaultValues(PUBLIC_EXPONENT));_this40.privateExponent=getParametersValue(parameters,PRIVATE_EXPONENT,RSAPrivateKey.defaultValues(PRIVATE_EXPONENT));_this40.prime1=getParametersValue(parameters,PRIME1,RSAPrivateKey.defaultValues(PRIME1));_this40.prime2=getParametersValue(parameters,PRIME2,RSAPrivateKey.defaultValues(PRIME2));_this40.exponent1=getParametersValue(parameters,EXPONENT1,RSAPrivateKey.defaultValues(EXPONENT1));_this40.exponent2=getParametersValue(parameters,EXPONENT2,RSAPrivateKey.defaultValues(EXPONENT2));_this40.coefficient=getParametersValue(parameters,COEFFICIENT,RSAPrivateKey.defaultValues(COEFFICIENT));if(OTHER_PRIME_INFOS in parameters){_this40.otherPrimeInfos=getParametersValue(parameters,OTHER_PRIME_INFOS,RSAPrivateKey.defaultValues(OTHER_PRIME_INFOS));}if(parameters.json){_this40.fromJSON(parameters.json);}if(parameters.schema){_this40.fromSchema(parameters.schema);}return _this40;}RSAPrivateKey.defaultValues=function defaultValues(memberName){switch(memberName){case VERSION$k:return 0;case MODULUS:return new Integer();case PUBLIC_EXPONENT:return new Integer();case PRIVATE_EXPONENT:return new Integer();case PRIME1:return new Integer();case PRIME2:return new Integer();case EXPONENT1:return new Integer();case EXPONENT2:return new Integer();case COEFFICIENT:return new Integer();case OTHER_PRIME_INFOS:return [];default:return _PkiObject36.defaultValues.call(this,memberName);}};RSAPrivateKey.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Integer({name:names.version||EMPTY_STRING}),new Integer({name:names.modulus||EMPTY_STRING}),new Integer({name:names.publicExponent||EMPTY_STRING}),new Integer({name:names.privateExponent||EMPTY_STRING}),new Integer({name:names.prime1||EMPTY_STRING}),new Integer({name:names.prime2||EMPTY_STRING}),new Integer({name:names.exponent1||EMPTY_STRING}),new Integer({name:names.exponent2||EMPTY_STRING}),new Integer({name:names.coefficient||EMPTY_STRING}),new Sequence({optional:true,value:[new Repeated({name:names.otherPrimeInfosName||EMPTY_STRING,value:OtherPrimeInfo.schema(names.otherPrimeInfo||{})})]})]});};var _proto37=RSAPrivateKey.prototype;_proto37.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$17);var asn1=compareSchema(schema,schema,RSAPrivateKey.schema({names:{version:VERSION$k,modulus:MODULUS,publicExponent:PUBLIC_EXPONENT,privateExponent:PRIVATE_EXPONENT,prime1:PRIME1,prime2:PRIME2,exponent1:EXPONENT1,exponent2:EXPONENT2,coefficient:COEFFICIENT,otherPrimeInfo:{names:{blockName:OTHER_PRIME_INFOS}}}}));AsnError.assertSchema(asn1,this.className);this.version=asn1.result.version.valueBlock.valueDec;this.modulus=asn1.result.modulus.convertFromDER(256);this.publicExponent=asn1.result.publicExponent;this.privateExponent=asn1.result.privateExponent.convertFromDER(256);this.prime1=asn1.result.prime1.convertFromDER(128);this.prime2=asn1.result.prime2.convertFromDER(128);this.exponent1=asn1.result.exponent1.convertFromDER(128);this.exponent2=asn1.result.exponent2.convertFromDER(128);this.coefficient=asn1.result.coefficient.convertFromDER(128);if(OTHER_PRIME_INFOS in asn1.result)this.otherPrimeInfos=Array.from(asn1.result.otherPrimeInfos,element=>new OtherPrimeInfo({schema:element}));};_proto37.toSchema=function toSchema(){var outputArray=[];outputArray.push(new Integer({value:this.version}));outputArray.push(this.modulus.convertToDER());outputArray.push(this.publicExponent);outputArray.push(this.privateExponent.convertToDER());outputArray.push(this.prime1.convertToDER());outputArray.push(this.prime2.convertToDER());outputArray.push(this.exponent1.convertToDER());outputArray.push(this.exponent2.convertToDER());outputArray.push(this.coefficient.convertToDER());if(this.otherPrimeInfos){outputArray.push(new Sequence({value:Array.from(this.otherPrimeInfos,o=>o.toSchema())}));}return new Sequence({value:outputArray});};_proto37.toJSON=function toJSON(){var jwk={n:Convert.ToBase64Url(this.modulus.valueBlock.valueHexView),e:Convert.ToBase64Url(this.publicExponent.valueBlock.valueHexView),d:Convert.ToBase64Url(this.privateExponent.valueBlock.valueHexView),p:Convert.ToBase64Url(this.prime1.valueBlock.valueHexView),q:Convert.ToBase64Url(this.prime2.valueBlock.valueHexView),dp:Convert.ToBase64Url(this.exponent1.valueBlock.valueHexView),dq:Convert.ToBase64Url(this.exponent2.valueBlock.valueHexView),qi:Convert.ToBase64Url(this.coefficient.valueBlock.valueHexView)};if(this.otherPrimeInfos){jwk.oth=Array.from(this.otherPrimeInfos,o=>o.toJSON());}return jwk;};_proto37.fromJSON=function fromJSON(json){ParameterError.assert("json",json,"n","e","d","p","q","dp","dq","qi");this.modulus=new Integer({valueHex:Convert.FromBase64Url(json.n)});this.publicExponent=new Integer({valueHex:Convert.FromBase64Url(json.e)});this.privateExponent=new Integer({valueHex:Convert.FromBase64Url(json.d)});this.prime1=new Integer({valueHex:Convert.FromBase64Url(json.p)});this.prime2=new Integer({valueHex:Convert.FromBase64Url(json.q)});this.exponent1=new Integer({valueHex:Convert.FromBase64Url(json.dp)});this.exponent2=new Integer({valueHex:Convert.FromBase64Url(json.dq)});this.coefficient=new Integer({valueHex:Convert.FromBase64Url(json.qi)});if(json.oth){this.otherPrimeInfos=Array.from(json.oth,element=>new OtherPrimeInfo({json:element}));}};return RSAPrivateKey;}(PkiObject);RSAPrivateKey.CLASS_NAME="RSAPrivateKey";var VERSION$j="version";var PRIVATE_KEY_ALGORITHM="privateKeyAlgorithm";var PRIVATE_KEY="privateKey";var ATTRIBUTES$5="attributes";var PARSED_KEY="parsedKey";var CLEAR_PROPS$16=[VERSION$j,PRIVATE_KEY_ALGORITHM,PRIVATE_KEY,ATTRIBUTES$5];var PrivateKeyInfo=/*#__PURE__*/function(_PkiObject37){_inheritsLoose(PrivateKeyInfo,_PkiObject37);function PrivateKeyInfo(parameters){var _this41;if(parameters===void 0){parameters={};}_this41=_PkiObject37.call(this)||this;_this41.version=getParametersValue(parameters,VERSION$j,PrivateKeyInfo.defaultValues(VERSION$j));_this41.privateKeyAlgorithm=getParametersValue(parameters,PRIVATE_KEY_ALGORITHM,PrivateKeyInfo.defaultValues(PRIVATE_KEY_ALGORITHM));_this41.privateKey=getParametersValue(parameters,PRIVATE_KEY,PrivateKeyInfo.defaultValues(PRIVATE_KEY));if(ATTRIBUTES$5 in parameters){_this41.attributes=getParametersValue(parameters,ATTRIBUTES$5,PrivateKeyInfo.defaultValues(ATTRIBUTES$5));}if(PARSED_KEY in parameters){_this41.parsedKey=getParametersValue(parameters,PARSED_KEY,PrivateKeyInfo.defaultValues(PARSED_KEY));}if(parameters.json){_this41.fromJSON(parameters.json);}if(parameters.schema){_this41.fromSchema(parameters.schema);}return _this41;}PrivateKeyInfo.defaultValues=function defaultValues(memberName){switch(memberName){case VERSION$j:return 0;case PRIVATE_KEY_ALGORITHM:return new AlgorithmIdentifier();case PRIVATE_KEY:return new OctetString();case ATTRIBUTES$5:return [];case PARSED_KEY:return {};default:return _PkiObject37.defaultValues.call(this,memberName);}};PrivateKeyInfo.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Integer({name:names.version||EMPTY_STRING}),AlgorithmIdentifier.schema(names.privateKeyAlgorithm||{}),new OctetString({name:names.privateKey||EMPTY_STRING}),new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:0},value:[new Repeated({name:names.attributes||EMPTY_STRING,value:Attribute.schema()})]})]});};var _proto38=PrivateKeyInfo.prototype;_proto38.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$16);var asn1=compareSchema(schema,schema,PrivateKeyInfo.schema({names:{version:VERSION$j,privateKeyAlgorithm:{names:{blockName:PRIVATE_KEY_ALGORITHM}},privateKey:PRIVATE_KEY,attributes:ATTRIBUTES$5}}));AsnError.assertSchema(asn1,this.className);this.version=asn1.result.version.valueBlock.valueDec;this.privateKeyAlgorithm=new AlgorithmIdentifier({schema:asn1.result.privateKeyAlgorithm});this.privateKey=asn1.result.privateKey;if(ATTRIBUTES$5 in asn1.result)this.attributes=Array.from(asn1.result.attributes,element=>new Attribute({schema:element}));switch(this.privateKeyAlgorithm.algorithmId){case"1.2.840.113549.1.1.1":{var privateKeyASN1=fromBER(this.privateKey.valueBlock.valueHexView);if(privateKeyASN1.offset!==-1)this.parsedKey=new RSAPrivateKey({schema:privateKeyASN1.result});}break;case"1.2.840.10045.2.1":if("algorithmParams"in this.privateKeyAlgorithm){if(this.privateKeyAlgorithm.algorithmParams instanceof ObjectIdentifier){var _privateKeyASN=fromBER(this.privateKey.valueBlock.valueHexView);if(_privateKeyASN.offset!==-1){this.parsedKey=new ECPrivateKey({namedCurve:this.privateKeyAlgorithm.algorithmParams.valueBlock.toString(),schema:_privateKeyASN.result});}}}break;}};_proto38.toSchema=function toSchema(){var outputArray=[new Integer({value:this.version}),this.privateKeyAlgorithm.toSchema(),this.privateKey];if(this.attributes){outputArray.push(new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:0},value:Array.from(this.attributes,o=>o.toSchema())}));}return new Sequence({value:outputArray});};_proto38.toJSON=function toJSON(){if(!this.parsedKey){var object={version:this.version,privateKeyAlgorithm:this.privateKeyAlgorithm.toJSON(),privateKey:this.privateKey.toJSON()};if(this.attributes){object.attributes=Array.from(this.attributes,o=>o.toJSON());}return object;}var jwk={};switch(this.privateKeyAlgorithm.algorithmId){case"1.2.840.10045.2.1":jwk.kty="EC";break;case"1.2.840.113549.1.1.1":jwk.kty="RSA";break;}var publicKeyJWK=this.parsedKey.toJSON();Object.assign(jwk,publicKeyJWK);return jwk;};_proto38.fromJSON=function fromJSON(json){if("kty"in json){switch(json.kty.toUpperCase()){case"EC":this.parsedKey=new ECPrivateKey({json});this.privateKeyAlgorithm=new AlgorithmIdentifier({algorithmId:"1.2.840.10045.2.1",algorithmParams:new ObjectIdentifier({value:this.parsedKey.namedCurve})});break;case"RSA":this.parsedKey=new RSAPrivateKey({json});this.privateKeyAlgorithm=new AlgorithmIdentifier({algorithmId:"1.2.840.113549.1.1.1",algorithmParams:new Null()});break;default:throw new Error(`Invalid value for "kty" parameter: ${json.kty}`);}this.privateKey=new OctetString({valueHex:this.parsedKey.toSchema().toBER(false)});}};return PrivateKeyInfo;}(PkiObject);PrivateKeyInfo.CLASS_NAME="PrivateKeyInfo";var CONTENT_TYPE$1="contentType";var CONTENT_ENCRYPTION_ALGORITHM="contentEncryptionAlgorithm";var ENCRYPTED_CONTENT="encryptedContent";var CLEAR_PROPS$15=[CONTENT_TYPE$1,CONTENT_ENCRYPTION_ALGORITHM,ENCRYPTED_CONTENT];var PIECE_SIZE=1024;var EncryptedContentInfo=/*#__PURE__*/function(_PkiObject38){_inheritsLoose(EncryptedContentInfo,_PkiObject38);function EncryptedContentInfo(parameters){var _this42;if(parameters===void 0){parameters={};}_this42=_PkiObject38.call(this)||this;_this42.contentType=getParametersValue(parameters,CONTENT_TYPE$1,EncryptedContentInfo.defaultValues(CONTENT_TYPE$1));_this42.contentEncryptionAlgorithm=getParametersValue(parameters,CONTENT_ENCRYPTION_ALGORITHM,EncryptedContentInfo.defaultValues(CONTENT_ENCRYPTION_ALGORITHM));if(ENCRYPTED_CONTENT in parameters&&parameters.encryptedContent){_this42.encryptedContent=parameters.encryptedContent;if(_this42.encryptedContent.idBlock.tagClass===1&&_this42.encryptedContent.idBlock.tagNumber===4){if(_this42.encryptedContent.idBlock.isConstructed===false&&!parameters.disableSplit){var constrString=new OctetString({idBlock:{isConstructed:true},isConstructed:true});var offset=0;var valueHex=_this42.encryptedContent.valueBlock.valueHexView.slice().buffer;var length=valueHex.byteLength;while(length>0){var pieceView=new Uint8Array(valueHex,offset,offset+PIECE_SIZE>valueHex.byteLength?valueHex.byteLength-offset:PIECE_SIZE);var _array=new ArrayBuffer(pieceView.length);var _view=new Uint8Array(_array);for(var i=0;i<_view.length;i++)_view[i]=pieceView[i];constrString.valueBlock.value.push(new OctetString({valueHex:_array}));length-=pieceView.length;offset+=pieceView.length;}_this42.encryptedContent=constrString;}}}if(parameters.schema){_this42.fromSchema(parameters.schema);}return _this42;}EncryptedContentInfo.defaultValues=function defaultValues(memberName){switch(memberName){case CONTENT_TYPE$1:return EMPTY_STRING;case CONTENT_ENCRYPTION_ALGORITHM:return new AlgorithmIdentifier();case ENCRYPTED_CONTENT:return new OctetString();default:return _PkiObject38.defaultValues.call(this,memberName);}};EncryptedContentInfo.compareWithDefault=function compareWithDefault(memberName,memberValue){switch(memberName){case CONTENT_TYPE$1:return memberValue===EMPTY_STRING;case CONTENT_ENCRYPTION_ALGORITHM:return memberValue.algorithmId===EMPTY_STRING&&"algorithmParams"in memberValue===false;case ENCRYPTED_CONTENT:return memberValue.isEqual(EncryptedContentInfo.defaultValues(ENCRYPTED_CONTENT));default:return _PkiObject38.defaultValues.call(this,memberName);}};EncryptedContentInfo.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new ObjectIdentifier({name:names.contentType||EMPTY_STRING}),AlgorithmIdentifier.schema(names.contentEncryptionAlgorithm||{}),new Choice({value:[new Constructed({name:names.encryptedContent||EMPTY_STRING,idBlock:{tagClass:3,tagNumber:0},value:[new Repeated({value:new OctetString()})]}),new Primitive({name:names.encryptedContent||EMPTY_STRING,idBlock:{tagClass:3,tagNumber:0}})]})]});};var _proto39=EncryptedContentInfo.prototype;_proto39.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$15);var asn1=compareSchema(schema,schema,EncryptedContentInfo.schema({names:{contentType:CONTENT_TYPE$1,contentEncryptionAlgorithm:{names:{blockName:CONTENT_ENCRYPTION_ALGORITHM}},encryptedContent:ENCRYPTED_CONTENT}}));AsnError.assertSchema(asn1,this.className);this.contentType=asn1.result.contentType.valueBlock.toString();this.contentEncryptionAlgorithm=new AlgorithmIdentifier({schema:asn1.result.contentEncryptionAlgorithm});if(ENCRYPTED_CONTENT in asn1.result){this.encryptedContent=asn1.result.encryptedContent;this.encryptedContent.idBlock.tagClass=1;this.encryptedContent.idBlock.tagNumber=4;}};_proto39.toSchema=function toSchema(){var sequenceLengthBlock={isIndefiniteForm:false};var outputArray=[];outputArray.push(new ObjectIdentifier({value:this.contentType}));outputArray.push(this.contentEncryptionAlgorithm.toSchema());if(this.encryptedContent){sequenceLengthBlock.isIndefiniteForm=this.encryptedContent.idBlock.isConstructed;var encryptedValue=this.encryptedContent;encryptedValue.idBlock.tagClass=3;encryptedValue.idBlock.tagNumber=0;encryptedValue.lenBlock.isIndefiniteForm=this.encryptedContent.idBlock.isConstructed;outputArray.push(encryptedValue);}return new Sequence({lenBlock:sequenceLengthBlock,value:outputArray});};_proto39.toJSON=function toJSON(){var res={contentType:this.contentType,contentEncryptionAlgorithm:this.contentEncryptionAlgorithm.toJSON()};if(this.encryptedContent){res.encryptedContent=this.encryptedContent.toJSON();}return res;};_proto39.getEncryptedContent=function getEncryptedContent(){if(!this.encryptedContent){throw new Error("Parameter 'encryptedContent' is undefined");}return OctetString.prototype.getValue.call(this.encryptedContent);};return EncryptedContentInfo;}(PkiObject);EncryptedContentInfo.CLASS_NAME="EncryptedContentInfo";var HASH_ALGORITHM$4="hashAlgorithm";var MASK_GEN_ALGORITHM$1="maskGenAlgorithm";var SALT_LENGTH="saltLength";var TRAILER_FIELD="trailerField";var CLEAR_PROPS$14=[HASH_ALGORITHM$4,MASK_GEN_ALGORITHM$1,SALT_LENGTH,TRAILER_FIELD];var RSASSAPSSParams=/*#__PURE__*/function(_PkiObject39){_inheritsLoose(RSASSAPSSParams,_PkiObject39);function RSASSAPSSParams(parameters){var _this43;if(parameters===void 0){parameters={};}_this43=_PkiObject39.call(this)||this;_this43.hashAlgorithm=getParametersValue(parameters,HASH_ALGORITHM$4,RSASSAPSSParams.defaultValues(HASH_ALGORITHM$4));_this43.maskGenAlgorithm=getParametersValue(parameters,MASK_GEN_ALGORITHM$1,RSASSAPSSParams.defaultValues(MASK_GEN_ALGORITHM$1));_this43.saltLength=getParametersValue(parameters,SALT_LENGTH,RSASSAPSSParams.defaultValues(SALT_LENGTH));_this43.trailerField=getParametersValue(parameters,TRAILER_FIELD,RSASSAPSSParams.defaultValues(TRAILER_FIELD));if(parameters.schema){_this43.fromSchema(parameters.schema);}return _this43;}RSASSAPSSParams.defaultValues=function defaultValues(memberName){switch(memberName){case HASH_ALGORITHM$4:return new AlgorithmIdentifier({algorithmId:"1.3.14.3.2.26",algorithmParams:new Null()});case MASK_GEN_ALGORITHM$1:return new AlgorithmIdentifier({algorithmId:"1.2.840.113549.1.1.8",algorithmParams:new AlgorithmIdentifier({algorithmId:"1.3.14.3.2.26",algorithmParams:new Null()}).toSchema()});case SALT_LENGTH:return 20;case TRAILER_FIELD:return 1;default:return _PkiObject39.defaultValues.call(this,memberName);}};RSASSAPSSParams.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Constructed({idBlock:{tagClass:3,tagNumber:0},optional:true,value:[AlgorithmIdentifier.schema(names.hashAlgorithm||{})]}),new Constructed({idBlock:{tagClass:3,tagNumber:1},optional:true,value:[AlgorithmIdentifier.schema(names.maskGenAlgorithm||{})]}),new Constructed({idBlock:{tagClass:3,tagNumber:2},optional:true,value:[new Integer({name:names.saltLength||EMPTY_STRING})]}),new Constructed({idBlock:{tagClass:3,tagNumber:3},optional:true,value:[new Integer({name:names.trailerField||EMPTY_STRING})]})]});};var _proto40=RSASSAPSSParams.prototype;_proto40.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$14);var asn1=compareSchema(schema,schema,RSASSAPSSParams.schema({names:{hashAlgorithm:{names:{blockName:HASH_ALGORITHM$4}},maskGenAlgorithm:{names:{blockName:MASK_GEN_ALGORITHM$1}},saltLength:SALT_LENGTH,trailerField:TRAILER_FIELD}}));AsnError.assertSchema(asn1,this.className);if(HASH_ALGORITHM$4 in asn1.result)this.hashAlgorithm=new AlgorithmIdentifier({schema:asn1.result.hashAlgorithm});if(MASK_GEN_ALGORITHM$1 in asn1.result)this.maskGenAlgorithm=new AlgorithmIdentifier({schema:asn1.result.maskGenAlgorithm});if(SALT_LENGTH in asn1.result)this.saltLength=asn1.result.saltLength.valueBlock.valueDec;if(TRAILER_FIELD in asn1.result)this.trailerField=asn1.result.trailerField.valueBlock.valueDec;};_proto40.toSchema=function toSchema(){var outputArray=[];if(!this.hashAlgorithm.isEqual(RSASSAPSSParams.defaultValues(HASH_ALGORITHM$4))){outputArray.push(new Constructed({idBlock:{tagClass:3,tagNumber:0},value:[this.hashAlgorithm.toSchema()]}));}if(!this.maskGenAlgorithm.isEqual(RSASSAPSSParams.defaultValues(MASK_GEN_ALGORITHM$1))){outputArray.push(new Constructed({idBlock:{tagClass:3,tagNumber:1},value:[this.maskGenAlgorithm.toSchema()]}));}if(this.saltLength!==RSASSAPSSParams.defaultValues(SALT_LENGTH)){outputArray.push(new Constructed({idBlock:{tagClass:3,tagNumber:2},value:[new Integer({value:this.saltLength})]}));}if(this.trailerField!==RSASSAPSSParams.defaultValues(TRAILER_FIELD)){outputArray.push(new Constructed({idBlock:{tagClass:3,tagNumber:3},value:[new Integer({value:this.trailerField})]}));}return new Sequence({value:outputArray});};_proto40.toJSON=function toJSON(){var res={};if(!this.hashAlgorithm.isEqual(RSASSAPSSParams.defaultValues(HASH_ALGORITHM$4))){res.hashAlgorithm=this.hashAlgorithm.toJSON();}if(!this.maskGenAlgorithm.isEqual(RSASSAPSSParams.defaultValues(MASK_GEN_ALGORITHM$1))){res.maskGenAlgorithm=this.maskGenAlgorithm.toJSON();}if(this.saltLength!==RSASSAPSSParams.defaultValues(SALT_LENGTH)){res.saltLength=this.saltLength;}if(this.trailerField!==RSASSAPSSParams.defaultValues(TRAILER_FIELD)){res.trailerField=this.trailerField;}return res;};return RSASSAPSSParams;}(PkiObject);RSASSAPSSParams.CLASS_NAME="RSASSAPSSParams";var SALT="salt";var ITERATION_COUNT="iterationCount";var KEY_LENGTH="keyLength";var PRF="prf";var CLEAR_PROPS$13=[SALT,ITERATION_COUNT,KEY_LENGTH,PRF];var PBKDF2Params=/*#__PURE__*/function(_PkiObject40){_inheritsLoose(PBKDF2Params,_PkiObject40);function PBKDF2Params(parameters){var _this44;if(parameters===void 0){parameters={};}_this44=_PkiObject40.call(this)||this;_this44.salt=getParametersValue(parameters,SALT,PBKDF2Params.defaultValues(SALT));_this44.iterationCount=getParametersValue(parameters,ITERATION_COUNT,PBKDF2Params.defaultValues(ITERATION_COUNT));if(KEY_LENGTH in parameters){_this44.keyLength=getParametersValue(parameters,KEY_LENGTH,PBKDF2Params.defaultValues(KEY_LENGTH));}if(PRF in parameters){_this44.prf=getParametersValue(parameters,PRF,PBKDF2Params.defaultValues(PRF));}if(parameters.schema){_this44.fromSchema(parameters.schema);}return _this44;}PBKDF2Params.defaultValues=function defaultValues(memberName){switch(memberName){case SALT:return {};case ITERATION_COUNT:return -1;case KEY_LENGTH:return 0;case PRF:return new AlgorithmIdentifier({algorithmId:"1.3.14.3.2.26",algorithmParams:new Null()});default:return _PkiObject40.defaultValues.call(this,memberName);}};PBKDF2Params.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Choice({value:[new OctetString({name:names.saltPrimitive||EMPTY_STRING}),AlgorithmIdentifier.schema(names.saltConstructed||{})]}),new Integer({name:names.iterationCount||EMPTY_STRING}),new Integer({name:names.keyLength||EMPTY_STRING,optional:true}),AlgorithmIdentifier.schema(names.prf||{names:{optional:true}})]});};var _proto41=PBKDF2Params.prototype;_proto41.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$13);var asn1=compareSchema(schema,schema,PBKDF2Params.schema({names:{saltPrimitive:SALT,saltConstructed:{names:{blockName:SALT}},iterationCount:ITERATION_COUNT,keyLength:KEY_LENGTH,prf:{names:{blockName:PRF,optional:true}}}}));AsnError.assertSchema(asn1,this.className);this.salt=asn1.result.salt;this.iterationCount=asn1.result.iterationCount.valueBlock.valueDec;if(KEY_LENGTH in asn1.result)this.keyLength=asn1.result.keyLength.valueBlock.valueDec;if(PRF in asn1.result)this.prf=new AlgorithmIdentifier({schema:asn1.result.prf});};_proto41.toSchema=function toSchema(){var outputArray=[];outputArray.push(this.salt);outputArray.push(new Integer({value:this.iterationCount}));if(KEY_LENGTH in this){if(PBKDF2Params.defaultValues(KEY_LENGTH)!==this.keyLength)outputArray.push(new Integer({value:this.keyLength}));}if(this.prf){if(PBKDF2Params.defaultValues(PRF).isEqual(this.prf)===false)outputArray.push(this.prf.toSchema());}return new Sequence({value:outputArray});};_proto41.toJSON=function toJSON(){var res={salt:this.salt.toJSON(),iterationCount:this.iterationCount};if(KEY_LENGTH in this){if(PBKDF2Params.defaultValues(KEY_LENGTH)!==this.keyLength)res.keyLength=this.keyLength;}if(this.prf){if(PBKDF2Params.defaultValues(PRF).isEqual(this.prf)===false)res.prf=this.prf.toJSON();}return res;};return PBKDF2Params;}(PkiObject);PBKDF2Params.CLASS_NAME="PBKDF2Params";var KEY_DERIVATION_FUNC="keyDerivationFunc";var ENCRYPTION_SCHEME="encryptionScheme";var CLEAR_PROPS$12=[KEY_DERIVATION_FUNC,ENCRYPTION_SCHEME];var PBES2Params=/*#__PURE__*/function(_PkiObject41){_inheritsLoose(PBES2Params,_PkiObject41);function PBES2Params(parameters){var _this45;if(parameters===void 0){parameters={};}_this45=_PkiObject41.call(this)||this;_this45.keyDerivationFunc=getParametersValue(parameters,KEY_DERIVATION_FUNC,PBES2Params.defaultValues(KEY_DERIVATION_FUNC));_this45.encryptionScheme=getParametersValue(parameters,ENCRYPTION_SCHEME,PBES2Params.defaultValues(ENCRYPTION_SCHEME));if(parameters.schema){_this45.fromSchema(parameters.schema);}return _this45;}PBES2Params.defaultValues=function defaultValues(memberName){switch(memberName){case KEY_DERIVATION_FUNC:return new AlgorithmIdentifier();case ENCRYPTION_SCHEME:return new AlgorithmIdentifier();default:return _PkiObject41.defaultValues.call(this,memberName);}};PBES2Params.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[AlgorithmIdentifier.schema(names.keyDerivationFunc||{}),AlgorithmIdentifier.schema(names.encryptionScheme||{})]});};var _proto42=PBES2Params.prototype;_proto42.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$12);var asn1=compareSchema(schema,schema,PBES2Params.schema({names:{keyDerivationFunc:{names:{blockName:KEY_DERIVATION_FUNC}},encryptionScheme:{names:{blockName:ENCRYPTION_SCHEME}}}}));AsnError.assertSchema(asn1,this.className);this.keyDerivationFunc=new AlgorithmIdentifier({schema:asn1.result.keyDerivationFunc});this.encryptionScheme=new AlgorithmIdentifier({schema:asn1.result.encryptionScheme});};_proto42.toSchema=function toSchema(){return new Sequence({value:[this.keyDerivationFunc.toSchema(),this.encryptionScheme.toSchema()]});};_proto42.toJSON=function toJSON(){return {keyDerivationFunc:this.keyDerivationFunc.toJSON(),encryptionScheme:this.encryptionScheme.toJSON()};};return PBES2Params;}(PkiObject);PBES2Params.CLASS_NAME="PBES2Params";var AbstractCryptoEngine=/*#__PURE__*/function(){function AbstractCryptoEngine(parameters){this.crypto=parameters.crypto;this.subtle="webkitSubtle"in parameters.crypto?parameters.crypto.webkitSubtle:parameters.crypto.subtle;this.name=getParametersValue(parameters,"name",EMPTY_STRING);}var _proto43=AbstractCryptoEngine.prototype;_proto43.encrypt=function encrypt(){try{var _this46$subtle;var _this46=this,_arguments=arguments;return _await((_this46$subtle=_this46.subtle).encrypt.apply(_this46$subtle,_arguments));}catch(e){return Promise.reject(e);}};_proto43.decrypt=function decrypt(){try{var _this47$subtle;var _this47=this,_arguments2=arguments;return _await((_this47$subtle=_this47.subtle).decrypt.apply(_this47$subtle,_arguments2));}catch(e){return Promise.reject(e);}};_proto43.sign=function sign(){var _this$subtle;return (_this$subtle=this.subtle).sign.apply(_this$subtle,arguments);};_proto43.verify=function verify(){try{var _this48$subtle;var _this48=this,_arguments3=arguments;return _await((_this48$subtle=_this48.subtle).verify.apply(_this48$subtle,_arguments3));}catch(e){return Promise.reject(e);}};_proto43.digest=function digest(){try{var _this49$subtle;var _this49=this,_arguments4=arguments;return _await((_this49$subtle=_this49.subtle).digest.apply(_this49$subtle,_arguments4));}catch(e){return Promise.reject(e);}};_proto43.generateKey=function generateKey(){try{var _this50$subtle;var _this50=this,_arguments5=arguments;return _await((_this50$subtle=_this50.subtle).generateKey.apply(_this50$subtle,_arguments5));}catch(e){return Promise.reject(e);}};_proto43.deriveKey=function deriveKey(){try{var _this51$subtle;var _this51=this,_arguments6=arguments;return _await((_this51$subtle=_this51.subtle).deriveKey.apply(_this51$subtle,_arguments6));}catch(e){return Promise.reject(e);}};_proto43.deriveBits=function deriveBits(){try{var _this52$subtle;var _this52=this,_arguments7=arguments;return _await((_this52$subtle=_this52.subtle).deriveBits.apply(_this52$subtle,_arguments7));}catch(e){return Promise.reject(e);}};_proto43.wrapKey=function wrapKey(){try{var _this53$subtle;var _this53=this,_arguments8=arguments;return _await((_this53$subtle=_this53.subtle).wrapKey.apply(_this53$subtle,_arguments8));}catch(e){return Promise.reject(e);}};_proto43.unwrapKey=function unwrapKey(){try{var _this54$subtle;var _this54=this,_arguments9=arguments;return _await((_this54$subtle=_this54.subtle).unwrapKey.apply(_this54$subtle,_arguments9));}catch(e){return Promise.reject(e);}};_proto43.exportKey=function exportKey(){var _this$subtle2;return (_this$subtle2=this.subtle).exportKey.apply(_this$subtle2,arguments);};_proto43.importKey=function importKey(){var _this$subtle3;return (_this$subtle3=this.subtle).importKey.apply(_this$subtle3,arguments);};_proto43.getRandomValues=function getRandomValues(array){return this.crypto.getRandomValues(array);};return AbstractCryptoEngine;}();function prepareAlgorithm(data){var res=typeof data==="string"?{name:data}:data;if("hash"in res){return Object.assign({},res,{hash:prepareAlgorithm(res.hash)});}return res;}var CryptoEngine=/*#__PURE__*/function(_AbstractCryptoEngine){_inheritsLoose(CryptoEngine,_AbstractCryptoEngine);function CryptoEngine(){return _AbstractCryptoEngine.apply(this,arguments)||this;}var _proto44=CryptoEngine.prototype;_proto44.importKey=function importKey(format,keyData,algorithm,extractable,keyUsages){try{var _this55=this;var _a,_b,_c,_d,_e,_f;var jwk={};var alg=prepareAlgorithm(algorithm);switch(format.toLowerCase()){case"raw":return _await(_this55.subtle.importKey("raw",keyData,algorithm,extractable,keyUsages));case"spki":{var asn1=fromBER(BufferSourceConverter.toArrayBuffer(keyData));AsnError.assert(asn1,"keyData");var publicKeyInfo=new PublicKeyInfo();try{publicKeyInfo.fromSchema(asn1.result);}catch(_unused2){throw new ArgumentError("Incorrect keyData");}switch(alg.name.toUpperCase()){case"RSA-PSS":{if(!alg.hash){throw new ParameterError("hash","algorithm.hash","Incorrect hash algorithm: Hash algorithm is missed");}switch(alg.hash.name.toUpperCase()){case"SHA-1":jwk.alg="PS1";break;case"SHA-256":jwk.alg="PS256";break;case"SHA-384":jwk.alg="PS384";break;case"SHA-512":jwk.alg="PS512";break;default:throw new Error(`Incorrect hash algorithm: ${alg.hash.name.toUpperCase()}`);}}case"RSASSA-PKCS1-V1_5":{keyUsages=["verify"];jwk.kty="RSA";jwk.ext=extractable;jwk.key_ops=keyUsages;if(publicKeyInfo.algorithm.algorithmId!=="1.2.840.113549.1.1.1")throw new Error(`Incorrect public key algorithm: ${publicKeyInfo.algorithm.algorithmId}`);if(!jwk.alg){if(!alg.hash){throw new ParameterError("hash","algorithm.hash","Incorrect hash algorithm: Hash algorithm is missed");}switch(alg.hash.name.toUpperCase()){case"SHA-1":jwk.alg="RS1";break;case"SHA-256":jwk.alg="RS256";break;case"SHA-384":jwk.alg="RS384";break;case"SHA-512":jwk.alg="RS512";break;default:throw new Error(`Incorrect hash algorithm: ${alg.hash.name.toUpperCase()}`);}}var publicKeyJSON=publicKeyInfo.toJSON();Object.assign(jwk,publicKeyJSON);}break;case"ECDSA":keyUsages=["verify"];case"ECDH":{jwk={kty:"EC",ext:extractable,key_ops:keyUsages};if(publicKeyInfo.algorithm.algorithmId!=="1.2.840.10045.2.1"){throw new Error(`Incorrect public key algorithm: ${publicKeyInfo.algorithm.algorithmId}`);}var _publicKeyJSON=publicKeyInfo.toJSON();Object.assign(jwk,_publicKeyJSON);}break;case"RSA-OAEP":{jwk.kty="RSA";jwk.ext=extractable;jwk.key_ops=keyUsages;if(_this55.name.toLowerCase()==="safari")jwk.alg="RSA-OAEP";else {if(!alg.hash){throw new ParameterError("hash","algorithm.hash","Incorrect hash algorithm: Hash algorithm is missed");}switch(alg.hash.name.toUpperCase()){case"SHA-1":jwk.alg="RSA-OAEP";break;case"SHA-256":jwk.alg="RSA-OAEP-256";break;case"SHA-384":jwk.alg="RSA-OAEP-384";break;case"SHA-512":jwk.alg="RSA-OAEP-512";break;default:throw new Error(`Incorrect hash algorithm: ${alg.hash.name.toUpperCase()}`);}}var _publicKeyJSON2=publicKeyInfo.toJSON();Object.assign(jwk,_publicKeyJSON2);}break;case"RSAES-PKCS1-V1_5":{jwk.kty="RSA";jwk.ext=extractable;jwk.key_ops=keyUsages;jwk.alg="PS1";var _publicKeyJSON3=publicKeyInfo.toJSON();Object.assign(jwk,_publicKeyJSON3);}break;default:throw new Error(`Incorrect algorithm name: ${alg.name.toUpperCase()}`);}}break;case"pkcs8":{var privateKeyInfo=new PrivateKeyInfo();var _asn=fromBER(BufferSourceConverter.toArrayBuffer(keyData));AsnError.assert(_asn,"keyData");try{privateKeyInfo.fromSchema(_asn.result);}catch(ex){throw new Error("Incorrect keyData");}if(!privateKeyInfo.parsedKey)throw new Error("Incorrect keyData");switch(alg.name.toUpperCase()){case"RSA-PSS":{switch((_a=alg.hash)===null||_a===void 0?void 0:_a.name.toUpperCase()){case"SHA-1":jwk.alg="PS1";break;case"SHA-256":jwk.alg="PS256";break;case"SHA-384":jwk.alg="PS384";break;case"SHA-512":jwk.alg="PS512";break;default:throw new Error(`Incorrect hash algorithm: ${(_b=alg.hash)===null||_b===void 0?void 0:_b.name.toUpperCase()}`);}}case"RSASSA-PKCS1-V1_5":{keyUsages=["sign"];jwk.kty="RSA";jwk.ext=extractable;jwk.key_ops=keyUsages;if(privateKeyInfo.privateKeyAlgorithm.algorithmId!=="1.2.840.113549.1.1.1")throw new Error(`Incorrect private key algorithm: ${privateKeyInfo.privateKeyAlgorithm.algorithmId}`);if("alg"in jwk===false){switch((_c=alg.hash)===null||_c===void 0?void 0:_c.name.toUpperCase()){case"SHA-1":jwk.alg="RS1";break;case"SHA-256":jwk.alg="RS256";break;case"SHA-384":jwk.alg="RS384";break;case"SHA-512":jwk.alg="RS512";break;default:throw new Error(`Incorrect hash algorithm: ${(_d=alg.hash)===null||_d===void 0?void 0:_d.name.toUpperCase()}`);}}var privateKeyJSON=privateKeyInfo.toJSON();Object.assign(jwk,privateKeyJSON);}break;case"ECDSA":keyUsages=["sign"];case"ECDH":{jwk={kty:"EC",ext:extractable,key_ops:keyUsages};if(privateKeyInfo.privateKeyAlgorithm.algorithmId!=="1.2.840.10045.2.1")throw new Error(`Incorrect algorithm: ${privateKeyInfo.privateKeyAlgorithm.algorithmId}`);var _privateKeyJSON=privateKeyInfo.toJSON();Object.assign(jwk,_privateKeyJSON);}break;case"RSA-OAEP":{jwk.kty="RSA";jwk.ext=extractable;jwk.key_ops=keyUsages;if(_this55.name.toLowerCase()==="safari")jwk.alg="RSA-OAEP";else {switch((_e=alg.hash)===null||_e===void 0?void 0:_e.name.toUpperCase()){case"SHA-1":jwk.alg="RSA-OAEP";break;case"SHA-256":jwk.alg="RSA-OAEP-256";break;case"SHA-384":jwk.alg="RSA-OAEP-384";break;case"SHA-512":jwk.alg="RSA-OAEP-512";break;default:throw new Error(`Incorrect hash algorithm: ${(_f=alg.hash)===null||_f===void 0?void 0:_f.name.toUpperCase()}`);}}var _privateKeyJSON2=privateKeyInfo.toJSON();Object.assign(jwk,_privateKeyJSON2);}break;case"RSAES-PKCS1-V1_5":{keyUsages=["decrypt"];jwk.kty="RSA";jwk.ext=extractable;jwk.key_ops=keyUsages;jwk.alg="PS1";var _privateKeyJSON3=privateKeyInfo.toJSON();Object.assign(jwk,_privateKeyJSON3);}break;default:throw new Error(`Incorrect algorithm name: ${alg.name.toUpperCase()}`);}}break;case"jwk":jwk=keyData;break;default:throw new Error(`Incorrect format: ${format}`);}if(_this55.name.toLowerCase()==="safari"){try{return _await(_this55.subtle.importKey("jwk",stringToArrayBuffer(JSON.stringify(jwk)),algorithm,extractable,keyUsages));}catch(_unused3){return _await(_this55.subtle.importKey("jwk",jwk,algorithm,extractable,keyUsages));}}return _await(_this55.subtle.importKey("jwk",jwk,algorithm,extractable,keyUsages));}catch(e){return Promise.reject(e);}};_proto44.exportKey=function exportKey(format,key){try{var _this56=this;return _await(_this56.subtle.exportKey("jwk",key),jwk=>{if(_this56.name.toLowerCase()==="safari"){if(jwk instanceof ArrayBuffer){jwk=JSON.parse(arrayBufferToString(jwk));}}switch(format.toLowerCase()){case"raw":return _this56.subtle.exportKey("raw",key);case"spki":{var publicKeyInfo=new PublicKeyInfo();try{publicKeyInfo.fromJSON(jwk);}catch(ex){throw new Error("Incorrect key data");}return publicKeyInfo.toSchema().toBER(false);}case"pkcs8":{var privateKeyInfo=new PrivateKeyInfo();try{privateKeyInfo.fromJSON(jwk);}catch(ex){throw new Error("Incorrect key data");}return privateKeyInfo.toSchema().toBER(false);}case"jwk":return jwk;default:throw new Error(`Incorrect format: ${format}`);}});}catch(e){return Promise.reject(e);}};_proto44.convert=function convert(inputFormat,outputFormat,keyData,algorithm,extractable,keyUsages){try{var _this57=this;if(inputFormat.toLowerCase()===outputFormat.toLowerCase()){return _await(keyData);}return _await(_this57.importKey(inputFormat,keyData,algorithm,extractable,keyUsages),key=>_this57.exportKey(outputFormat,key));}catch(e){return Promise.reject(e);}};_proto44.getAlgorithmByOID=function getAlgorithmByOID(oid,safety,target){if(safety===void 0){safety=false;}switch(oid){case"1.2.840.113549.1.1.1":return {name:"RSAES-PKCS1-v1_5"};case"1.2.840.113549.1.1.5":return {name:"RSASSA-PKCS1-v1_5",hash:{name:"SHA-1"}};case"1.2.840.113549.1.1.11":return {name:"RSASSA-PKCS1-v1_5",hash:{name:"SHA-256"}};case"1.2.840.113549.1.1.12":return {name:"RSASSA-PKCS1-v1_5",hash:{name:"SHA-384"}};case"1.2.840.113549.1.1.13":return {name:"RSASSA-PKCS1-v1_5",hash:{name:"SHA-512"}};case"1.2.840.113549.1.1.10":return {name:"RSA-PSS"};case"1.2.840.113549.1.1.7":return {name:"RSA-OAEP"};case"1.2.840.10045.2.1":case"1.2.840.10045.4.1":return {name:"ECDSA",hash:{name:"SHA-1"}};case"1.2.840.10045.4.3.2":return {name:"ECDSA",hash:{name:"SHA-256"}};case"1.2.840.10045.4.3.3":return {name:"ECDSA",hash:{name:"SHA-384"}};case"1.2.840.10045.4.3.4":return {name:"ECDSA",hash:{name:"SHA-512"}};case"1.3.133.16.840.63.0.2":return {name:"ECDH",kdf:"SHA-1"};case"1.3.132.1.11.1":return {name:"ECDH",kdf:"SHA-256"};case"1.3.132.1.11.2":return {name:"ECDH",kdf:"SHA-384"};case"1.3.132.1.11.3":return {name:"ECDH",kdf:"SHA-512"};case"2.16.840.1.101.3.4.1.2":return {name:"AES-CBC",length:128};case"2.16.840.1.101.3.4.1.22":return {name:"AES-CBC",length:192};case"2.16.840.1.101.3.4.1.42":return {name:"AES-CBC",length:256};case"2.16.840.1.101.3.4.1.6":return {name:"AES-GCM",length:128};case"2.16.840.1.101.3.4.1.26":return {name:"AES-GCM",length:192};case"2.16.840.1.101.3.4.1.46":return {name:"AES-GCM",length:256};case"2.16.840.1.101.3.4.1.4":return {name:"AES-CFB",length:128};case"2.16.840.1.101.3.4.1.24":return {name:"AES-CFB",length:192};case"2.16.840.1.101.3.4.1.44":return {name:"AES-CFB",length:256};case"2.16.840.1.101.3.4.1.5":return {name:"AES-KW",length:128};case"2.16.840.1.101.3.4.1.25":return {name:"AES-KW",length:192};case"2.16.840.1.101.3.4.1.45":return {name:"AES-KW",length:256};case"1.2.840.113549.2.7":return {name:"HMAC",hash:{name:"SHA-1"}};case"1.2.840.113549.2.9":return {name:"HMAC",hash:{name:"SHA-256"}};case"1.2.840.113549.2.10":return {name:"HMAC",hash:{name:"SHA-384"}};case"1.2.840.113549.2.11":return {name:"HMAC",hash:{name:"SHA-512"}};case"1.2.840.113549.1.9.16.3.5":return {name:"DH"};case"1.3.14.3.2.26":return {name:"SHA-1"};case"2.16.840.1.101.3.4.2.1":return {name:"SHA-256"};case"2.16.840.1.101.3.4.2.2":return {name:"SHA-384"};case"2.16.840.1.101.3.4.2.3":return {name:"SHA-512"};case"1.2.840.113549.1.5.12":return {name:"PBKDF2"};case"1.2.840.10045.3.1.7":return {name:"P-256"};case"1.3.132.0.34":return {name:"P-384"};case"1.3.132.0.35":return {name:"P-521"};}if(safety){throw new Error(`Unsupported algorithm identifier ${target?`for ${target} `:EMPTY_STRING}: ${oid}`);}return {};};_proto44.getOIDByAlgorithm=function getOIDByAlgorithm(algorithm,safety,target){if(safety===void 0){safety=false;}var result=EMPTY_STRING;switch(algorithm.name.toUpperCase()){case"RSAES-PKCS1-V1_5":result="1.2.840.113549.1.1.1";break;case"RSASSA-PKCS1-V1_5":switch(algorithm.hash.name.toUpperCase()){case"SHA-1":result="1.2.840.113549.1.1.5";break;case"SHA-256":result="1.2.840.113549.1.1.11";break;case"SHA-384":result="1.2.840.113549.1.1.12";break;case"SHA-512":result="1.2.840.113549.1.1.13";break;}break;case"RSA-PSS":result="1.2.840.113549.1.1.10";break;case"RSA-OAEP":result="1.2.840.113549.1.1.7";break;case"ECDSA":switch(algorithm.hash.name.toUpperCase()){case"SHA-1":result="1.2.840.10045.4.1";break;case"SHA-256":result="1.2.840.10045.4.3.2";break;case"SHA-384":result="1.2.840.10045.4.3.3";break;case"SHA-512":result="1.2.840.10045.4.3.4";break;}break;case"ECDH":switch(algorithm.kdf.toUpperCase()){case"SHA-1":result="1.3.133.16.840.63.0.2";break;case"SHA-256":result="1.3.132.1.11.1";break;case"SHA-384":result="1.3.132.1.11.2";break;case"SHA-512":result="1.3.132.1.11.3";break;}break;case"AES-CTR":break;case"AES-CBC":switch(algorithm.length){case 128:result="2.16.840.1.101.3.4.1.2";break;case 192:result="2.16.840.1.101.3.4.1.22";break;case 256:result="2.16.840.1.101.3.4.1.42";break;}break;case"AES-CMAC":break;case"AES-GCM":switch(algorithm.length){case 128:result="2.16.840.1.101.3.4.1.6";break;case 192:result="2.16.840.1.101.3.4.1.26";break;case 256:result="2.16.840.1.101.3.4.1.46";break;}break;case"AES-CFB":switch(algorithm.length){case 128:result="2.16.840.1.101.3.4.1.4";break;case 192:result="2.16.840.1.101.3.4.1.24";break;case 256:result="2.16.840.1.101.3.4.1.44";break;}break;case"AES-KW":switch(algorithm.length){case 128:result="2.16.840.1.101.3.4.1.5";break;case 192:result="2.16.840.1.101.3.4.1.25";break;case 256:result="2.16.840.1.101.3.4.1.45";break;}break;case"HMAC":switch(algorithm.hash.name.toUpperCase()){case"SHA-1":result="1.2.840.113549.2.7";break;case"SHA-256":result="1.2.840.113549.2.9";break;case"SHA-384":result="1.2.840.113549.2.10";break;case"SHA-512":result="1.2.840.113549.2.11";break;}break;case"DH":result="1.2.840.113549.1.9.16.3.5";break;case"SHA-1":result="1.3.14.3.2.26";break;case"SHA-256":result="2.16.840.1.101.3.4.2.1";break;case"SHA-384":result="2.16.840.1.101.3.4.2.2";break;case"SHA-512":result="2.16.840.1.101.3.4.2.3";break;case"CONCAT":break;case"HKDF":break;case"PBKDF2":result="1.2.840.113549.1.5.12";break;case"P-256":result="1.2.840.10045.3.1.7";break;case"P-384":result="1.3.132.0.34";break;case"P-521":result="1.3.132.0.35";break;}if(!result&&safety){throw new Error(`Unsupported algorithm ${target?`for ${target} `:EMPTY_STRING}: ${algorithm.name}`);}return result;};_proto44.getAlgorithmParameters=function getAlgorithmParameters(algorithmName,operation){var result={algorithm:{},usages:[]};switch(algorithmName.toUpperCase()){case"RSAES-PKCS1-V1_5":case"RSASSA-PKCS1-V1_5":switch(operation.toLowerCase()){case"generatekey":result={algorithm:{name:"RSASSA-PKCS1-v1_5",modulusLength:2048,publicExponent:new Uint8Array([0x01,0x00,0x01]),hash:{name:"SHA-256"}},usages:["sign","verify"]};break;case"verify":case"sign":case"importkey":result={algorithm:{name:"RSASSA-PKCS1-v1_5",hash:{name:"SHA-256"}},usages:["verify"]};break;case"exportkey":default:return {algorithm:{name:"RSASSA-PKCS1-v1_5"},usages:[]};}break;case"RSA-PSS":switch(operation.toLowerCase()){case"sign":case"verify":result={algorithm:{name:"RSA-PSS",hash:{name:"SHA-1"},saltLength:20},usages:["sign","verify"]};break;case"generatekey":result={algorithm:{name:"RSA-PSS",modulusLength:2048,publicExponent:new Uint8Array([0x01,0x00,0x01]),hash:{name:"SHA-1"}},usages:["sign","verify"]};break;case"importkey":result={algorithm:{name:"RSA-PSS",hash:{name:"SHA-1"}},usages:["verify"]};break;case"exportkey":default:return {algorithm:{name:"RSA-PSS"},usages:[]};}break;case"RSA-OAEP":switch(operation.toLowerCase()){case"encrypt":case"decrypt":result={algorithm:{name:"RSA-OAEP"},usages:["encrypt","decrypt"]};break;case"generatekey":result={algorithm:{name:"RSA-OAEP",modulusLength:2048,publicExponent:new Uint8Array([0x01,0x00,0x01]),hash:{name:"SHA-256"}},usages:["encrypt","decrypt","wrapKey","unwrapKey"]};break;case"importkey":result={algorithm:{name:"RSA-OAEP",hash:{name:"SHA-256"}},usages:["encrypt"]};break;case"exportkey":default:return {algorithm:{name:"RSA-OAEP"},usages:[]};}break;case"ECDSA":switch(operation.toLowerCase()){case"generatekey":result={algorithm:{name:"ECDSA",namedCurve:"P-256"},usages:["sign","verify"]};break;case"importkey":result={algorithm:{name:"ECDSA",namedCurve:"P-256"},usages:["verify"]};break;case"verify":case"sign":result={algorithm:{name:"ECDSA",hash:{name:"SHA-256"}},usages:["sign"]};break;default:return {algorithm:{name:"ECDSA"},usages:[]};}break;case"ECDH":switch(operation.toLowerCase()){case"exportkey":case"importkey":case"generatekey":result={algorithm:{name:"ECDH",namedCurve:"P-256"},usages:["deriveKey","deriveBits"]};break;case"derivekey":case"derivebits":result={algorithm:{name:"ECDH",namedCurve:"P-256",public:[]},usages:["encrypt","decrypt"]};break;default:return {algorithm:{name:"ECDH"},usages:[]};}break;case"AES-CTR":switch(operation.toLowerCase()){case"importkey":case"exportkey":case"generatekey":result={algorithm:{name:"AES-CTR",length:256},usages:["encrypt","decrypt","wrapKey","unwrapKey"]};break;case"decrypt":case"encrypt":result={algorithm:{name:"AES-CTR",counter:new Uint8Array(16),length:10},usages:["encrypt","decrypt","wrapKey","unwrapKey"]};break;default:return {algorithm:{name:"AES-CTR"},usages:[]};}break;case"AES-CBC":switch(operation.toLowerCase()){case"importkey":case"exportkey":case"generatekey":result={algorithm:{name:"AES-CBC",length:256},usages:["encrypt","decrypt","wrapKey","unwrapKey"]};break;case"decrypt":case"encrypt":result={algorithm:{name:"AES-CBC",iv:this.getRandomValues(new Uint8Array(16))},usages:["encrypt","decrypt","wrapKey","unwrapKey"]};break;default:return {algorithm:{name:"AES-CBC"},usages:[]};}break;case"AES-GCM":switch(operation.toLowerCase()){case"importkey":case"exportkey":case"generatekey":result={algorithm:{name:"AES-GCM",length:256},usages:["encrypt","decrypt","wrapKey","unwrapKey"]};break;case"decrypt":case"encrypt":result={algorithm:{name:"AES-GCM",iv:this.getRandomValues(new Uint8Array(16))},usages:["encrypt","decrypt","wrapKey","unwrapKey"]};break;default:return {algorithm:{name:"AES-GCM"},usages:[]};}break;case"AES-KW":switch(operation.toLowerCase()){case"importkey":case"exportkey":case"generatekey":case"wrapkey":case"unwrapkey":result={algorithm:{name:"AES-KW",length:256},usages:["wrapKey","unwrapKey"]};break;default:return {algorithm:{name:"AES-KW"},usages:[]};}break;case"HMAC":switch(operation.toLowerCase()){case"sign":case"verify":result={algorithm:{name:"HMAC"},usages:["sign","verify"]};break;case"importkey":case"exportkey":case"generatekey":result={algorithm:{name:"HMAC",length:32,hash:{name:"SHA-256"}},usages:["sign","verify"]};break;default:return {algorithm:{name:"HMAC"},usages:[]};}break;case"HKDF":switch(operation.toLowerCase()){case"derivekey":result={algorithm:{name:"HKDF",hash:"SHA-256",salt:new Uint8Array([]),info:new Uint8Array([])},usages:["encrypt","decrypt"]};break;default:return {algorithm:{name:"HKDF"},usages:[]};}break;case"PBKDF2":switch(operation.toLowerCase()){case"derivekey":result={algorithm:{name:"PBKDF2",hash:{name:"SHA-256"},salt:new Uint8Array([]),iterations:10000},usages:["encrypt","decrypt"]};break;default:return {algorithm:{name:"PBKDF2"},usages:[]};}break;}return result;};_proto44.getHashAlgorithm=function getHashAlgorithm(signatureAlgorithm){var result=EMPTY_STRING;switch(signatureAlgorithm.algorithmId){case"1.2.840.10045.4.1":case"1.2.840.113549.1.1.5":result="SHA-1";break;case"1.2.840.10045.4.3.2":case"1.2.840.113549.1.1.11":result="SHA-256";break;case"1.2.840.10045.4.3.3":case"1.2.840.113549.1.1.12":result="SHA-384";break;case"1.2.840.10045.4.3.4":case"1.2.840.113549.1.1.13":result="SHA-512";break;case"1.2.840.113549.1.1.10":{try{var params=new RSASSAPSSParams({schema:signatureAlgorithm.algorithmParams});if(params.hashAlgorithm){var algorithm=this.getAlgorithmByOID(params.hashAlgorithm.algorithmId);if("name"in algorithm){result=algorithm.name;}else {return EMPTY_STRING;}}else result="SHA-1";}catch(_unused4){}}break;}return result;};_proto44.encryptEncryptedContentInfo=function encryptEncryptedContentInfo(parameters){try{var _this58=this;ParameterError.assert(parameters,"password","contentEncryptionAlgorithm","hmacHashAlgorithm","iterationCount","contentToEncrypt","contentToEncrypt","contentType");var contentEncryptionOID=_this58.getOIDByAlgorithm(parameters.contentEncryptionAlgorithm,true,"contentEncryptionAlgorithm");var pbkdf2OID=_this58.getOIDByAlgorithm({name:"PBKDF2"},true,"PBKDF2");var hmacOID=_this58.getOIDByAlgorithm({name:"HMAC",hash:{name:parameters.hmacHashAlgorithm}},true,"hmacHashAlgorithm");var ivBuffer=new ArrayBuffer(16);var ivView=new Uint8Array(ivBuffer);_this58.getRandomValues(ivView);var saltBuffer=new ArrayBuffer(64);var saltView=new Uint8Array(saltBuffer);_this58.getRandomValues(saltView);var contentView=new Uint8Array(parameters.contentToEncrypt);var pbkdf2Params=new PBKDF2Params({salt:new OctetString({valueHex:saltBuffer}),iterationCount:parameters.iterationCount,prf:new AlgorithmIdentifier({algorithmId:hmacOID,algorithmParams:new Null()})});var passwordView=new Uint8Array(parameters.password);return _await(_this58.importKey("raw",passwordView,"PBKDF2",false,["deriveKey"]),pbkdfKey=>_await(_this58.deriveKey({name:"PBKDF2",hash:{name:parameters.hmacHashAlgorithm},salt:saltView,iterations:parameters.iterationCount},pbkdfKey,parameters.contentEncryptionAlgorithm,false,["encrypt"]),derivedKey=>_await(_this58.encrypt({name:parameters.contentEncryptionAlgorithm.name,iv:ivView},derivedKey,contentView),encryptedData=>{var pbes2Parameters=new PBES2Params({keyDerivationFunc:new AlgorithmIdentifier({algorithmId:pbkdf2OID,algorithmParams:pbkdf2Params.toSchema()}),encryptionScheme:new AlgorithmIdentifier({algorithmId:contentEncryptionOID,algorithmParams:new OctetString({valueHex:ivBuffer})})});return new EncryptedContentInfo({contentType:parameters.contentType,contentEncryptionAlgorithm:new AlgorithmIdentifier({algorithmId:"1.2.840.113549.1.5.13",algorithmParams:pbes2Parameters.toSchema()}),encryptedContent:new OctetString({valueHex:encryptedData})});})));}catch(e){return Promise.reject(e);}};_proto44.decryptEncryptedContentInfo=function decryptEncryptedContentInfo(parameters){try{var _this59=this;ParameterError.assert(parameters,"password","encryptedContentInfo");if(parameters.encryptedContentInfo.contentEncryptionAlgorithm.algorithmId!=="1.2.840.113549.1.5.13")throw new Error(`Unknown "contentEncryptionAlgorithm": ${parameters.encryptedContentInfo.contentEncryptionAlgorithm.algorithmId}`);var pbes2Parameters;try{pbes2Parameters=new PBES2Params({schema:parameters.encryptedContentInfo.contentEncryptionAlgorithm.algorithmParams});}catch(ex){throw new Error("Incorrectly encoded \"pbes2Parameters\"");}var pbkdf2Params;try{pbkdf2Params=new PBKDF2Params({schema:pbes2Parameters.keyDerivationFunc.algorithmParams});}catch(ex){throw new Error("Incorrectly encoded \"pbkdf2Params\"");}var contentEncryptionAlgorithm=_this59.getAlgorithmByOID(pbes2Parameters.encryptionScheme.algorithmId,true);var ivBuffer=pbes2Parameters.encryptionScheme.algorithmParams.valueBlock.valueHex;var ivView=new Uint8Array(ivBuffer);var saltBuffer=pbkdf2Params.salt.valueBlock.valueHex;var saltView=new Uint8Array(saltBuffer);var iterationCount=pbkdf2Params.iterationCount;var hmacHashAlgorithm="SHA-1";if(pbkdf2Params.prf){var algorithm=_this59.getAlgorithmByOID(pbkdf2Params.prf.algorithmId,true);hmacHashAlgorithm=algorithm.hash.name;}return _await(_this59.importKey("raw",parameters.password,"PBKDF2",false,["deriveKey"]),pbkdfKey=>_await(_this59.deriveKey({name:"PBKDF2",hash:{name:hmacHashAlgorithm},salt:saltView,iterations:iterationCount},pbkdfKey,contentEncryptionAlgorithm,false,["decrypt"]),result=>{var dataBuffer=parameters.encryptedContentInfo.getEncryptedContent();return _this59.decrypt({name:contentEncryptionAlgorithm.name,iv:ivView},result,dataBuffer);}));}catch(e){return Promise.reject(e);}};_proto44.stampDataWithPassword=function stampDataWithPassword(parameters){try{var _this60=this;if(parameters instanceof Object===false)throw new Error("Parameters must have type \"Object\"");ParameterError.assert(parameters,"password","hashAlgorithm","iterationCount","salt","contentToStamp");var length;switch(parameters.hashAlgorithm.toLowerCase()){case"sha-1":length=160;break;case"sha-256":length=256;break;case"sha-384":length=384;break;case"sha-512":length=512;break;default:throw new Error(`Incorrect "parameters.hashAlgorithm" parameter: ${parameters.hashAlgorithm}`);}var hmacAlgorithm={name:"HMAC",length,hash:{name:parameters.hashAlgorithm}};return _await(makePKCS12B2Key(_this60,parameters.hashAlgorithm,length,parameters.password,parameters.salt,parameters.iterationCount),pkcsKey=>_await(_this60.importKey("raw",new Uint8Array(pkcsKey),hmacAlgorithm,false,["sign"]),hmacKey=>_this60.sign(hmacAlgorithm,hmacKey,new Uint8Array(parameters.contentToStamp))));}catch(e){return Promise.reject(e);}};_proto44.verifyDataStampedWithPassword=function verifyDataStampedWithPassword(parameters){try{var _this61=this;ParameterError.assert(parameters,"password","hashAlgorithm","salt","iterationCount","contentToVerify","signatureToVerify");var length=0;switch(parameters.hashAlgorithm.toLowerCase()){case"sha-1":length=160;break;case"sha-256":length=256;break;case"sha-384":length=384;break;case"sha-512":length=512;break;default:throw new Error(`Incorrect "parameters.hashAlgorithm" parameter: ${parameters.hashAlgorithm}`);}var hmacAlgorithm={name:"HMAC",length,hash:{name:parameters.hashAlgorithm}};return _await(makePKCS12B2Key(_this61,parameters.hashAlgorithm,length,parameters.password,parameters.salt,parameters.iterationCount),pkcsKey=>_await(_this61.importKey("raw",new Uint8Array(pkcsKey),hmacAlgorithm,false,["verify"]),hmacKey=>_this61.verify(hmacAlgorithm,hmacKey,new Uint8Array(parameters.signatureToVerify),new Uint8Array(parameters.contentToVerify))));}catch(e){return Promise.reject(e);}};_proto44.getSignatureParameters=function getSignatureParameters(privateKey,hashAlgorithm){try{var _this62=this;if(hashAlgorithm===void 0){hashAlgorithm="SHA-1";}_this62.getOIDByAlgorithm({name:hashAlgorithm},true,"hashAlgorithm");var signatureAlgorithm=new AlgorithmIdentifier();var parameters=_this62.getAlgorithmParameters(privateKey.algorithm.name,"sign");if(!Object.keys(parameters.algorithm).length){throw new Error("Parameter 'algorithm' is empty");}var algorithm=parameters.algorithm;algorithm.hash.name=hashAlgorithm;switch(privateKey.algorithm.name.toUpperCase()){case"RSASSA-PKCS1-V1_5":case"ECDSA":signatureAlgorithm.algorithmId=_this62.getOIDByAlgorithm(algorithm,true);break;case"RSA-PSS":{switch(hashAlgorithm.toUpperCase()){case"SHA-256":algorithm.saltLength=32;break;case"SHA-384":algorithm.saltLength=48;break;case"SHA-512":algorithm.saltLength=64;break;}var paramsObject={};if(hashAlgorithm.toUpperCase()!=="SHA-1"){var hashAlgorithmOID=_this62.getOIDByAlgorithm({name:hashAlgorithm},true,"hashAlgorithm");paramsObject.hashAlgorithm=new AlgorithmIdentifier({algorithmId:hashAlgorithmOID,algorithmParams:new Null()});paramsObject.maskGenAlgorithm=new AlgorithmIdentifier({algorithmId:"1.2.840.113549.1.1.8",algorithmParams:paramsObject.hashAlgorithm.toSchema()});}if(algorithm.saltLength!==20)paramsObject.saltLength=algorithm.saltLength;var pssParameters=new RSASSAPSSParams(paramsObject);signatureAlgorithm.algorithmId="1.2.840.113549.1.1.10";signatureAlgorithm.algorithmParams=pssParameters.toSchema();}break;default:throw new Error(`Unsupported signature algorithm: ${privateKey.algorithm.name}`);}return _await({signatureAlgorithm,parameters});}catch(e){return Promise.reject(e);}};_proto44.signWithPrivateKey=function signWithPrivateKey(data,privateKey,parameters){try{var _this63=this;return _await(_this63.sign(parameters.algorithm,privateKey,data),signature=>parameters.algorithm.name==="ECDSA"?createCMSECDSASignature(signature):signature);}catch(e){return Promise.reject(e);}};_proto44.fillPublicKeyParameters=function fillPublicKeyParameters(publicKeyInfo,signatureAlgorithm){var parameters={};var shaAlgorithm=this.getHashAlgorithm(signatureAlgorithm);if(shaAlgorithm===EMPTY_STRING)throw new Error(`Unsupported signature algorithm: ${signatureAlgorithm.algorithmId}`);var algorithmId;if(signatureAlgorithm.algorithmId==="1.2.840.113549.1.1.10")algorithmId=signatureAlgorithm.algorithmId;else algorithmId=publicKeyInfo.algorithm.algorithmId;var algorithmObject=this.getAlgorithmByOID(algorithmId,true);parameters.algorithm=this.getAlgorithmParameters(algorithmObject.name,"importKey");if("hash"in parameters.algorithm.algorithm)parameters.algorithm.algorithm.hash.name=shaAlgorithm;if(algorithmObject.name==="ECDSA"){var publicKeyAlgorithm=publicKeyInfo.algorithm;if(!publicKeyAlgorithm.algorithmParams){throw new Error("Algorithm parameters for ECDSA public key are missed");}var publicKeyAlgorithmParams=publicKeyAlgorithm.algorithmParams;if("idBlock"in publicKeyAlgorithm.algorithmParams){if(!(publicKeyAlgorithmParams.idBlock.tagClass===1&&publicKeyAlgorithmParams.idBlock.tagNumber===6)){throw new Error("Incorrect type for ECDSA public key parameters");}}var curveObject=this.getAlgorithmByOID(publicKeyAlgorithmParams.valueBlock.toString(),true);parameters.algorithm.algorithm.namedCurve=curveObject.name;}return parameters;};_proto44.getPublicKey=function getPublicKey(publicKeyInfo,signatureAlgorithm,parameters){try{var _this64=this;if(!parameters){parameters=_this64.fillPublicKeyParameters(publicKeyInfo,signatureAlgorithm);}var publicKeyInfoBuffer=publicKeyInfo.toSchema().toBER(false);return _await(_this64.importKey("spki",publicKeyInfoBuffer,parameters.algorithm.algorithm,true,parameters.algorithm.usages));}catch(e){return Promise.reject(e);}};_proto44.verifyWithPublicKey=function verifyWithPublicKey(data,signature,publicKeyInfo,signatureAlgorithm,shaAlgorithm){try{var _exit=false;var _this65=this;var publicKey;return _await(_invoke(()=>{if(!shaAlgorithm){shaAlgorithm=_this65.getHashAlgorithm(signatureAlgorithm);if(!shaAlgorithm)throw new Error(`Unsupported signature algorithm: ${signatureAlgorithm.algorithmId}`);return _await(_this65.getPublicKey(publicKeyInfo,signatureAlgorithm),_this65$getPublicKey=>{publicKey=_this65$getPublicKey;});}else {var parameters={};var algorithmId;if(signatureAlgorithm.algorithmId==="1.2.840.113549.1.1.10")algorithmId=signatureAlgorithm.algorithmId;else algorithmId=publicKeyInfo.algorithm.algorithmId;var algorithmObject=_this65.getAlgorithmByOID(algorithmId,true);parameters.algorithm=_this65.getAlgorithmParameters(algorithmObject.name,"importKey");if("hash"in parameters.algorithm.algorithm)parameters.algorithm.algorithm.hash.name=shaAlgorithm;if(algorithmObject.name==="ECDSA"){var algorithmParamsChecked=false;if("algorithmParams"in publicKeyInfo.algorithm===true){if("idBlock"in publicKeyInfo.algorithm.algorithmParams){if(publicKeyInfo.algorithm.algorithmParams.idBlock.tagClass===1&&publicKeyInfo.algorithm.algorithmParams.idBlock.tagNumber===6)algorithmParamsChecked=true;}}if(algorithmParamsChecked===false){throw new Error("Incorrect type for ECDSA public key parameters");}var curveObject=_this65.getAlgorithmByOID(publicKeyInfo.algorithm.algorithmParams.valueBlock.toString(),true);parameters.algorithm.algorithm.namedCurve=curveObject.name;}return _await(_this65.getPublicKey(publicKeyInfo,null,parameters),_this65$getPublicKey2=>{publicKey=_this65$getPublicKey2;});}},_result2=>{if(_exit)return _result2;var algorithm=_this65.getAlgorithmParameters(publicKey.algorithm.name,"verify");if("hash"in algorithm.algorithm)algorithm.algorithm.hash.name=shaAlgorithm;var signatureValue=signature.valueBlock.valueHexView;if(publicKey.algorithm.name==="ECDSA"){var namedCurve=ECNamedCurves.find(publicKey.algorithm.namedCurve);if(!namedCurve){throw new Error("Unsupported named curve in use");}var asn1=fromBER(signatureValue);AsnError.assert(asn1,"Signature value");signatureValue=createECDSASignatureFromCMS(asn1.result,namedCurve.size);}if(publicKey.algorithm.name==="RSA-PSS"){var pssParameters=new RSASSAPSSParams({schema:signatureAlgorithm.algorithmParams});if("saltLength"in pssParameters)algorithm.algorithm.saltLength=pssParameters.saltLength;else algorithm.algorithm.saltLength=20;var hashAlgo="SHA-1";if("hashAlgorithm"in pssParameters){var hashAlgorithm=_this65.getAlgorithmByOID(pssParameters.hashAlgorithm.algorithmId,true);hashAlgo=hashAlgorithm.name;}algorithm.algorithm.hash.name=hashAlgo;}return _this65.verify(algorithm.algorithm,publicKey,signatureValue,data);}));}catch(e){return Promise.reject(e);}};return CryptoEngine;}(AbstractCryptoEngine);var engine={name:"none",crypto:null};function isCryptoEngine(engine){return engine&&typeof engine==="object"&&"crypto"in engine?true:false;}function setEngine(name){var crypto=null;if((arguments.length<=1?0:arguments.length-1)<2){if(arguments.length<=1?0:arguments.length-1){crypto=arguments.length<=1?undefined:arguments[1];}else {crypto=typeof self!=="undefined"&&self.crypto?new CryptoEngine({name:"browser",crypto:self.crypto}):null;}}else {var cryptoArg=arguments.length<=1?undefined:arguments[1];var subtleArg=arguments.length<=2?undefined:arguments[2];if(isCryptoEngine(subtleArg)){crypto=subtleArg;}else if(isCryptoEngine(cryptoArg)){crypto=cryptoArg;}else if("subtle"in cryptoArg&&"getRandomValues"in cryptoArg){crypto=new CryptoEngine({crypto:cryptoArg});}}if(typeof process!=="undefined"&&"pid"in process&&typeof global!=="undefined"&&typeof window==="undefined"){if(typeof global[process.pid]==="undefined"){global[process.pid]={};}else {if(typeof global[process.pid]!=="object"){throw new Error(`Name global.${process.pid} already exists and it is not an object`);}}if(typeof global[process.pid].pkijs==="undefined"){global[process.pid].pkijs={};}else {if(typeof global[process.pid].pkijs!=="object"){throw new Error(`Name global.${process.pid}.pkijs already exists and it is not an object`);}}global[process.pid].pkijs.engine={name:name,crypto};}else {engine={name:name,crypto};}}function getEngine(){if(typeof process!=="undefined"&&"pid"in process&&typeof global!=="undefined"&&typeof window==="undefined"){var _engine;try{_engine=global[process.pid].pkijs.engine;}catch(ex){throw new Error("Please call 'setEngine' before call to 'getEngine'");}return _engine;}return engine;}function getCrypto(safety){if(safety===void 0){safety=false;}var _engine=getEngine();if(!_engine.crypto&&safety){throw new Error("Unable to create WebCrypto object");}return _engine.crypto;}function getOIDByAlgorithm(algorithm,safety,target){return getCrypto(true).getOIDByAlgorithm(algorithm,safety,target);}function getAlgorithmParameters(algorithmName,operation){return getCrypto(true).getAlgorithmParameters(algorithmName,operation);}function createCMSECDSASignature(signatureBuffer){if(signatureBuffer.byteLength%2!==0)return EMPTY_BUFFER;var length=signatureBuffer.byteLength/2;var rBuffer=new ArrayBuffer(length);var rView=new Uint8Array(rBuffer);rView.set(new Uint8Array(signatureBuffer,0,length));var rInteger=new Integer({valueHex:rBuffer});var sBuffer=new ArrayBuffer(length);var sView=new Uint8Array(sBuffer);sView.set(new Uint8Array(signatureBuffer,length,length));var sInteger=new Integer({valueHex:sBuffer});return new Sequence({value:[rInteger.convertToDER(),sInteger.convertToDER()]}).toBER(false);}function createECDSASignatureFromCMS(cmsSignature,pointSize){if(!(cmsSignature instanceof Sequence&&cmsSignature.valueBlock.value.length===2&&cmsSignature.valueBlock.value[0]instanceof Integer&&cmsSignature.valueBlock.value[1]instanceof Integer))return EMPTY_BUFFER;var rValueView=cmsSignature.valueBlock.value[0].convertFromDER().valueBlock.valueHexView;var sValueView=cmsSignature.valueBlock.value[1].convertFromDER().valueBlock.valueHexView;var res=new Uint8Array(pointSize*2);res.set(rValueView,pointSize-rValueView.byteLength);res.set(sValueView,2*pointSize-sValueView.byteLength);return res.buffer;}var VERSION$i="version";var LOG_ID="logID";var EXTENSIONS$6="extensions";var TIMESTAMP="timestamp";var HASH_ALGORITHM$3="hashAlgorithm";var SIGNATURE_ALGORITHM$8="signatureAlgorithm";var SIGNATURE$7="signature";var NONE="none";var MD5="md5";var SHA1="sha1";var SHA224="sha224";var SHA256="sha256";var SHA384="sha384";var SHA512="sha512";var ANONYMOUS="anonymous";var RSA="rsa";var DSA="dsa";var ECDSA="ecdsa";var SignedCertificateTimestamp=/*#__PURE__*/function(_PkiObject42){_inheritsLoose(SignedCertificateTimestamp,_PkiObject42);function SignedCertificateTimestamp(parameters){var _this66;if(parameters===void 0){parameters={};}_this66=_PkiObject42.call(this)||this;_this66.version=getParametersValue(parameters,VERSION$i,SignedCertificateTimestamp.defaultValues(VERSION$i));_this66.logID=getParametersValue(parameters,LOG_ID,SignedCertificateTimestamp.defaultValues(LOG_ID));_this66.timestamp=getParametersValue(parameters,TIMESTAMP,SignedCertificateTimestamp.defaultValues(TIMESTAMP));_this66.extensions=getParametersValue(parameters,EXTENSIONS$6,SignedCertificateTimestamp.defaultValues(EXTENSIONS$6));_this66.hashAlgorithm=getParametersValue(parameters,HASH_ALGORITHM$3,SignedCertificateTimestamp.defaultValues(HASH_ALGORITHM$3));_this66.signatureAlgorithm=getParametersValue(parameters,SIGNATURE_ALGORITHM$8,SignedCertificateTimestamp.defaultValues(SIGNATURE_ALGORITHM$8));_this66.signature=getParametersValue(parameters,SIGNATURE$7,SignedCertificateTimestamp.defaultValues(SIGNATURE$7));if("stream"in parameters&&parameters.stream){_this66.fromStream(parameters.stream);}if(parameters.schema){_this66.fromSchema(parameters.schema);}return _this66;}SignedCertificateTimestamp.defaultValues=function defaultValues(memberName){switch(memberName){case VERSION$i:return 0;case LOG_ID:case EXTENSIONS$6:return EMPTY_BUFFER;case TIMESTAMP:return new Date(0);case HASH_ALGORITHM$3:case SIGNATURE_ALGORITHM$8:return EMPTY_STRING;case SIGNATURE$7:return new Any();default:return _PkiObject42.defaultValues.call(this,memberName);}};var _proto45=SignedCertificateTimestamp.prototype;_proto45.fromSchema=function fromSchema(schema){if(schema instanceof RawData===false)throw new Error("Object's schema was not verified against input data for SignedCertificateTimestamp");var seqStream=new SeqStream({stream:new ByteStream({buffer:schema.data})});this.fromStream(seqStream);};_proto45.fromStream=function fromStream(stream){var blockLength=stream.getUint16();this.version=stream.getBlock(1)[0];if(this.version===0){this.logID=new Uint8Array(stream.getBlock(32)).buffer.slice(0);this.timestamp=new Date(utilFromBase(new Uint8Array(stream.getBlock(8)),8));var extensionsLength=stream.getUint16();this.extensions=new Uint8Array(stream.getBlock(extensionsLength)).buffer.slice(0);switch(stream.getBlock(1)[0]){case 0:this.hashAlgorithm=NONE;break;case 1:this.hashAlgorithm=MD5;break;case 2:this.hashAlgorithm=SHA1;break;case 3:this.hashAlgorithm=SHA224;break;case 4:this.hashAlgorithm=SHA256;break;case 5:this.hashAlgorithm=SHA384;break;case 6:this.hashAlgorithm=SHA512;break;default:throw new Error("Object's stream was not correct for SignedCertificateTimestamp");}switch(stream.getBlock(1)[0]){case 0:this.signatureAlgorithm=ANONYMOUS;break;case 1:this.signatureAlgorithm=RSA;break;case 2:this.signatureAlgorithm=DSA;break;case 3:this.signatureAlgorithm=ECDSA;break;default:throw new Error("Object's stream was not correct for SignedCertificateTimestamp");}var signatureLength=stream.getUint16();var signatureData=new Uint8Array(stream.getBlock(signatureLength)).buffer.slice(0);var asn1=fromBER(signatureData);AsnError.assert(asn1,"SignedCertificateTimestamp");this.signature=asn1.result;if(blockLength!==47+extensionsLength+signatureLength){throw new Error("Object's stream was not correct for SignedCertificateTimestamp");}}};_proto45.toSchema=function toSchema(){var stream=this.toStream();return new RawData({data:stream.stream.buffer});};_proto45.toStream=function toStream(){var stream=new SeqStream();stream.appendUint16(47+this.extensions.byteLength+this.signature.valueBeforeDecodeView.byteLength);stream.appendChar(this.version);stream.appendView(new Uint8Array(this.logID));var timeBuffer=new ArrayBuffer(8);var timeView=new Uint8Array(timeBuffer);var baseArray=utilToBase(this.timestamp.valueOf(),8);timeView.set(new Uint8Array(baseArray),8-baseArray.byteLength);stream.appendView(timeView);stream.appendUint16(this.extensions.byteLength);if(this.extensions.byteLength)stream.appendView(new Uint8Array(this.extensions));var _hashAlgorithm;switch(this.hashAlgorithm.toLowerCase()){case NONE:_hashAlgorithm=0;break;case MD5:_hashAlgorithm=1;break;case SHA1:_hashAlgorithm=2;break;case SHA224:_hashAlgorithm=3;break;case SHA256:_hashAlgorithm=4;break;case SHA384:_hashAlgorithm=5;break;case SHA512:_hashAlgorithm=6;break;default:throw new Error(`Incorrect data for hashAlgorithm: ${this.hashAlgorithm}`);}stream.appendChar(_hashAlgorithm);var _signatureAlgorithm;switch(this.signatureAlgorithm.toLowerCase()){case ANONYMOUS:_signatureAlgorithm=0;break;case RSA:_signatureAlgorithm=1;break;case DSA:_signatureAlgorithm=2;break;case ECDSA:_signatureAlgorithm=3;break;default:throw new Error(`Incorrect data for signatureAlgorithm: ${this.signatureAlgorithm}`);}stream.appendChar(_signatureAlgorithm);var _signature=this.signature.toBER(false);stream.appendUint16(_signature.byteLength);stream.appendView(new Uint8Array(_signature));return stream;};_proto45.toJSON=function toJSON(){return {version:this.version,logID:bufferToHexCodes(this.logID),timestamp:this.timestamp,extensions:bufferToHexCodes(this.extensions),hashAlgorithm:this.hashAlgorithm,signatureAlgorithm:this.signatureAlgorithm,signature:this.signature.toJSON()};};_proto45.verify=function verify(logs,data,dataType,crypto){try{var _this67=this;if(dataType===void 0){dataType=0;}if(crypto===void 0){crypto=getCrypto(true);}var logId=toBase64(arrayBufferToString(_this67.logID));var publicKeyBase64=null;var stream=new SeqStream();for(var _i10=0;_i10<logs.length;_i10++){var log=logs[_i10];if(log.log_id===logId){publicKeyBase64=log.key;break;}}if(!publicKeyBase64){throw new Error(`Public key not found for CT with logId: ${logId}`);}var pki=stringToArrayBuffer(fromBase64(publicKeyBase64));var publicKeyInfo=PublicKeyInfo.fromBER(pki);stream.appendChar(0x00);stream.appendChar(0x00);var timeBuffer=new ArrayBuffer(8);var timeView=new Uint8Array(timeBuffer);var baseArray=utilToBase(_this67.timestamp.valueOf(),8);timeView.set(new Uint8Array(baseArray),8-baseArray.byteLength);stream.appendView(timeView);stream.appendUint16(dataType);if(dataType===0)stream.appendUint24(data.byteLength);stream.appendView(new Uint8Array(data));stream.appendUint16(_this67.extensions.byteLength);if(_this67.extensions.byteLength!==0)stream.appendView(new Uint8Array(_this67.extensions));return _await(crypto.verifyWithPublicKey(stream.buffer.slice(0,stream.length),new OctetString({valueHex:_this67.signature.toBER(false)}),publicKeyInfo,{algorithmId:EMPTY_STRING},"SHA-256"));}catch(e){return Promise.reject(e);}};return SignedCertificateTimestamp;}(PkiObject);SignedCertificateTimestamp.CLASS_NAME="SignedCertificateTimestamp";var TIMESTAMPS="timestamps";var SignedCertificateTimestampList=/*#__PURE__*/function(_PkiObject43){_inheritsLoose(SignedCertificateTimestampList,_PkiObject43);function SignedCertificateTimestampList(parameters){var _this68;if(parameters===void 0){parameters={};}_this68=_PkiObject43.call(this)||this;_this68.timestamps=getParametersValue(parameters,TIMESTAMPS,SignedCertificateTimestampList.defaultValues(TIMESTAMPS));if(parameters.schema){_this68.fromSchema(parameters.schema);}return _this68;}SignedCertificateTimestampList.defaultValues=function defaultValues(memberName){switch(memberName){case TIMESTAMPS:return [];default:return _PkiObject43.defaultValues.call(this,memberName);}};SignedCertificateTimestampList.compareWithDefault=function compareWithDefault(memberName,memberValue){switch(memberName){case TIMESTAMPS:return memberValue.length===0;default:return _PkiObject43.defaultValues.call(this,memberName);}};SignedCertificateTimestampList.schema=function schema(parameters){if(parameters===void 0){parameters={};}var _a;var names=getParametersValue(parameters,"names",{});(_a=names.optional)!==null&&_a!==void 0?_a:names.optional=false;return new OctetString({name:names.blockName||"SignedCertificateTimestampList",optional:names.optional});};var _proto46=SignedCertificateTimestampList.prototype;_proto46.fromSchema=function fromSchema(schema){if(schema instanceof OctetString===false){throw new Error("Object's schema was not verified against input data for SignedCertificateTimestampList");}var seqStream=new SeqStream({stream:new ByteStream({buffer:schema.valueBlock.valueHex})});var dataLength=seqStream.getUint16();if(dataLength!==seqStream.length){throw new Error("Object's schema was not verified against input data for SignedCertificateTimestampList");}while(seqStream.length){this.timestamps.push(new SignedCertificateTimestamp({stream:seqStream}));}};_proto46.toSchema=function toSchema(){var stream=new SeqStream();var overallLength=0;var timestampsData=[];for(var _i12=0,_this$timestamps2=this.timestamps;_i12<_this$timestamps2.length;_i12++){var timestamp=_this$timestamps2[_i12];var timestampStream=timestamp.toStream();timestampsData.push(timestampStream);overallLength+=timestampStream.stream.buffer.byteLength;}stream.appendUint16(overallLength);for(var _i14=0;_i14<timestampsData.length;_i14++){var _timestamp=timestampsData[_i14];stream.appendView(_timestamp.stream.view);}return new OctetString({valueHex:stream.stream.buffer.slice(0)});};_proto46.toJSON=function toJSON(){return {timestamps:Array.from(this.timestamps,o=>o.toJSON())};};return SignedCertificateTimestampList;}(PkiObject);SignedCertificateTimestampList.CLASS_NAME="SignedCertificateTimestampList";var ATTRIBUTES$4="attributes";var CLEAR_PROPS$11=[ATTRIBUTES$4];var SubjectDirectoryAttributes=/*#__PURE__*/function(_PkiObject44){_inheritsLoose(SubjectDirectoryAttributes,_PkiObject44);function SubjectDirectoryAttributes(parameters){var _this69;if(parameters===void 0){parameters={};}_this69=_PkiObject44.call(this)||this;_this69.attributes=getParametersValue(parameters,ATTRIBUTES$4,SubjectDirectoryAttributes.defaultValues(ATTRIBUTES$4));if(parameters.schema){_this69.fromSchema(parameters.schema);}return _this69;}SubjectDirectoryAttributes.defaultValues=function defaultValues(memberName){switch(memberName){case ATTRIBUTES$4:return [];default:return _PkiObject44.defaultValues.call(this,memberName);}};SubjectDirectoryAttributes.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new Repeated({name:names.attributes||EMPTY_STRING,value:Attribute.schema()})]});};var _proto47=SubjectDirectoryAttributes.prototype;_proto47.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$11);var asn1=compareSchema(schema,schema,SubjectDirectoryAttributes.schema({names:{attributes:ATTRIBUTES$4}}));AsnError.assertSchema(asn1,this.className);this.attributes=Array.from(asn1.result.attributes,element=>new Attribute({schema:element}));};_proto47.toSchema=function toSchema(){return new Sequence({value:Array.from(this.attributes,o=>o.toSchema())});};_proto47.toJSON=function toJSON(){return {attributes:Array.from(this.attributes,o=>o.toJSON())};};return SubjectDirectoryAttributes;}(PkiObject);SubjectDirectoryAttributes.CLASS_NAME="SubjectDirectoryAttributes";var ExtensionValueFactory=/*#__PURE__*/function(){function ExtensionValueFactory(){}ExtensionValueFactory.getItems=function getItems(){if(!this.types){this.types={};ExtensionValueFactory.register(id_SubjectAltName,"SubjectAltName",AltName);ExtensionValueFactory.register(id_IssuerAltName,"IssuerAltName",AltName);ExtensionValueFactory.register(id_AuthorityKeyIdentifier,"AuthorityKeyIdentifier",AuthorityKeyIdentifier);ExtensionValueFactory.register(id_BasicConstraints,"BasicConstraints",BasicConstraints);ExtensionValueFactory.register(id_MicrosoftCaVersion,"MicrosoftCaVersion",CAVersion);ExtensionValueFactory.register(id_CertificatePolicies,"CertificatePolicies",CertificatePolicies);ExtensionValueFactory.register(id_MicrosoftAppPolicies,"CertificatePoliciesMicrosoft",CertificatePolicies);ExtensionValueFactory.register(id_MicrosoftCertTemplateV2,"MicrosoftCertTemplateV2",CertificateTemplate);ExtensionValueFactory.register(id_CRLDistributionPoints,"CRLDistributionPoints",CRLDistributionPoints);ExtensionValueFactory.register(id_FreshestCRL,"FreshestCRL",CRLDistributionPoints);ExtensionValueFactory.register(id_ExtKeyUsage,"ExtKeyUsage",ExtKeyUsage);ExtensionValueFactory.register(id_CertificateIssuer,"CertificateIssuer",GeneralNames);ExtensionValueFactory.register(id_AuthorityInfoAccess,"AuthorityInfoAccess",InfoAccess);ExtensionValueFactory.register(id_SubjectInfoAccess,"SubjectInfoAccess",InfoAccess);ExtensionValueFactory.register(id_IssuingDistributionPoint,"IssuingDistributionPoint",IssuingDistributionPoint);ExtensionValueFactory.register(id_NameConstraints,"NameConstraints",NameConstraints);ExtensionValueFactory.register(id_PolicyConstraints,"PolicyConstraints",PolicyConstraints);ExtensionValueFactory.register(id_PolicyMappings,"PolicyMappings",PolicyMappings);ExtensionValueFactory.register(id_PrivateKeyUsagePeriod,"PrivateKeyUsagePeriod",PrivateKeyUsagePeriod);ExtensionValueFactory.register(id_QCStatements,"QCStatements",QCStatements);ExtensionValueFactory.register(id_SignedCertificateTimestampList,"SignedCertificateTimestampList",SignedCertificateTimestampList);ExtensionValueFactory.register(id_SubjectDirectoryAttributes,"SubjectDirectoryAttributes",SubjectDirectoryAttributes);}return this.types;};ExtensionValueFactory.fromBER=function fromBER$1(id,raw){var asn1=fromBER(raw);if(asn1.offset===-1){return null;}var item=this.find(id);if(item){try{return new item.type({schema:asn1.result});}catch(ex){var res=new item.type();res.parsingError=`Incorrectly formatted value of extension ${item.name} (${id})`;return res;}}return asn1.result;};ExtensionValueFactory.find=function find(id){var types=this.getItems();return types[id]||null;};ExtensionValueFactory.register=function register(id,name,type){this.getItems()[id]={name,type};};return ExtensionValueFactory;}();var EXTN_ID="extnID";var CRITICAL="critical";var EXTN_VALUE="extnValue";var PARSED_VALUE$5="parsedValue";var CLEAR_PROPS$10=[EXTN_ID,CRITICAL,EXTN_VALUE];var Extension=/*#__PURE__*/function(_PkiObject45){_inheritsLoose(Extension,_PkiObject45);function Extension(parameters){var _this70;if(parameters===void 0){parameters={};}_this70=_PkiObject45.call(this)||this;_this70.extnID=getParametersValue(parameters,EXTN_ID,Extension.defaultValues(EXTN_ID));_this70.critical=getParametersValue(parameters,CRITICAL,Extension.defaultValues(CRITICAL));if(EXTN_VALUE in parameters){_this70.extnValue=new OctetString({valueHex:parameters.extnValue});}else {_this70.extnValue=Extension.defaultValues(EXTN_VALUE);}if(PARSED_VALUE$5 in parameters){_this70.parsedValue=getParametersValue(parameters,PARSED_VALUE$5,Extension.defaultValues(PARSED_VALUE$5));}if(parameters.schema){_this70.fromSchema(parameters.schema);}return _this70;}Extension.defaultValues=function defaultValues(memberName){switch(memberName){case EXTN_ID:return EMPTY_STRING;case CRITICAL:return false;case EXTN_VALUE:return new OctetString();case PARSED_VALUE$5:return {};default:return _PkiObject45.defaultValues.call(this,memberName);}};Extension.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[new ObjectIdentifier({name:names.extnID||EMPTY_STRING}),new Boolean$1({name:names.critical||EMPTY_STRING,optional:true}),new OctetString({name:names.extnValue||EMPTY_STRING})]});};var _proto48=Extension.prototype;_proto48.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$10);var asn1=compareSchema(schema,schema,Extension.schema({names:{extnID:EXTN_ID,critical:CRITICAL,extnValue:EXTN_VALUE}}));AsnError.assertSchema(asn1,this.className);this.extnID=asn1.result.extnID.valueBlock.toString();if(CRITICAL in asn1.result){this.critical=asn1.result.critical.valueBlock.value;}this.extnValue=asn1.result.extnValue;};_proto48.toSchema=function toSchema(){var outputArray=[];outputArray.push(new ObjectIdentifier({value:this.extnID}));if(this.critical!==Extension.defaultValues(CRITICAL)){outputArray.push(new Boolean$1({value:this.critical}));}outputArray.push(this.extnValue);return new Sequence({value:outputArray});};_proto48.toJSON=function toJSON(){var object={extnID:this.extnID,extnValue:this.extnValue.toJSON()};if(this.critical!==Extension.defaultValues(CRITICAL)){object.critical=this.critical;}if(this.parsedValue&&this.parsedValue.toJSON){object.parsedValue=this.parsedValue.toJSON();}return object;};_createClass(Extension,[{key:"parsedValue",get:function(){if(this._parsedValue===undefined){var parsedValue=ExtensionValueFactory.fromBER(this.extnID,this.extnValue.valueBlock.valueHexView);this._parsedValue=parsedValue;}return this._parsedValue||undefined;},set:function(value){this._parsedValue=value;}}]);return Extension;}(PkiObject);Extension.CLASS_NAME="Extension";var EXTENSIONS$5="extensions";var CLEAR_PROPS$$=[EXTENSIONS$5];var Extensions=/*#__PURE__*/function(_PkiObject46){_inheritsLoose(Extensions,_PkiObject46);function Extensions(parameters){var _this71;if(parameters===void 0){parameters={};}_this71=_PkiObject46.call(this)||this;_this71.extensions=getParametersValue(parameters,EXTENSIONS$5,Extensions.defaultValues(EXTENSIONS$5));if(parameters.schema){_this71.fromSchema(parameters.schema);}return _this71;}Extensions.defaultValues=function defaultValues(memberName){switch(memberName){case EXTENSIONS$5:return [];default:return _PkiObject46.defaultValues.call(this,memberName);}};Extensions.schema=function schema(parameters,optional){if(parameters===void 0){parameters={};}if(optional===void 0){optional=false;}var names=getParametersValue(parameters,"names",{});return new Sequence({optional,name:names.blockName||EMPTY_STRING,value:[new Repeated({name:names.extensions||EMPTY_STRING,value:Extension.schema(names.extension||{})})]});};var _proto49=Extensions.prototype;_proto49.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$$);var asn1=compareSchema(schema,schema,Extensions.schema({names:{extensions:EXTENSIONS$5}}));AsnError.assertSchema(asn1,this.className);this.extensions=Array.from(asn1.result.extensions,element=>new Extension({schema:element}));};_proto49.toSchema=function toSchema(){return new Sequence({value:Array.from(this.extensions,o=>o.toSchema())});};_proto49.toJSON=function toJSON(){return {extensions:this.extensions.map(o=>o.toJSON())};};return Extensions;}(PkiObject);Extensions.CLASS_NAME="Extensions";var TYPE$1="type";var VALUE$4="value";var UTC_TIME_NAME="utcTimeName";var GENERAL_TIME_NAME="generalTimeName";var CLEAR_PROPS$R=[UTC_TIME_NAME,GENERAL_TIME_NAME];var TimeType;(function(TimeType){TimeType[TimeType["UTCTime"]=0]="UTCTime";TimeType[TimeType["GeneralizedTime"]=1]="GeneralizedTime";TimeType[TimeType["empty"]=2]="empty";})(TimeType||(TimeType={}));var Time=/*#__PURE__*/function(_PkiObject56){_inheritsLoose(Time,_PkiObject56);function Time(parameters){var _this81;if(parameters===void 0){parameters={};}_this81=_PkiObject56.call(this)||this;_this81.type=getParametersValue(parameters,TYPE$1,Time.defaultValues(TYPE$1));_this81.value=getParametersValue(parameters,VALUE$4,Time.defaultValues(VALUE$4));if(parameters.schema){_this81.fromSchema(parameters.schema);}return _this81;}Time.defaultValues=function defaultValues(memberName){switch(memberName){case TYPE$1:return 0;case VALUE$4:return new Date(0,0,0);default:return _PkiObject56.defaultValues.call(this,memberName);}};Time.schema=function schema(parameters,optional){if(parameters===void 0){parameters={};}if(optional===void 0){optional=false;}var names=getParametersValue(parameters,"names",{});return new Choice({optional,value:[new UTCTime({name:names.utcTimeName||EMPTY_STRING}),new GeneralizedTime({name:names.generalTimeName||EMPTY_STRING})]});};var _proto59=Time.prototype;_proto59.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$R);var asn1=compareSchema(schema,schema,Time.schema({names:{utcTimeName:UTC_TIME_NAME,generalTimeName:GENERAL_TIME_NAME}}));AsnError.assertSchema(asn1,this.className);if(UTC_TIME_NAME in asn1.result){this.type=0;this.value=asn1.result.utcTimeName.toDate();}if(GENERAL_TIME_NAME in asn1.result){this.type=1;this.value=asn1.result.generalTimeName.toDate();}};_proto59.toSchema=function toSchema(){if(this.type===0){return new UTCTime({valueDate:this.value});}else if(this.type===1){return new GeneralizedTime({valueDate:this.value});}return {};};_proto59.toJSON=function toJSON(){return {type:this.type,value:this.value};};return Time;}(PkiObject);Time.CLASS_NAME="Time";var TBS$4="tbs";var VERSION$f="version";var SERIAL_NUMBER$3="serialNumber";var SIGNATURE$4="signature";var ISSUER$2="issuer";var NOT_BEFORE="notBefore";var NOT_AFTER="notAfter";var SUBJECT$1="subject";var SUBJECT_PUBLIC_KEY_INFO="subjectPublicKeyInfo";var ISSUER_UNIQUE_ID="issuerUniqueID";var SUBJECT_UNIQUE_ID="subjectUniqueID";var EXTENSIONS$2="extensions";var SIGNATURE_ALGORITHM$5="signatureAlgorithm";var SIGNATURE_VALUE$2="signatureValue";var TBS_CERTIFICATE="tbsCertificate";var TBS_CERTIFICATE_VERSION=`${TBS_CERTIFICATE}.${VERSION$f}`;var TBS_CERTIFICATE_SERIAL_NUMBER=`${TBS_CERTIFICATE}.${SERIAL_NUMBER$3}`;var TBS_CERTIFICATE_SIGNATURE=`${TBS_CERTIFICATE}.${SIGNATURE$4}`;var TBS_CERTIFICATE_ISSUER=`${TBS_CERTIFICATE}.${ISSUER$2}`;var TBS_CERTIFICATE_NOT_BEFORE=`${TBS_CERTIFICATE}.${NOT_BEFORE}`;var TBS_CERTIFICATE_NOT_AFTER=`${TBS_CERTIFICATE}.${NOT_AFTER}`;var TBS_CERTIFICATE_SUBJECT=`${TBS_CERTIFICATE}.${SUBJECT$1}`;var TBS_CERTIFICATE_SUBJECT_PUBLIC_KEY=`${TBS_CERTIFICATE}.${SUBJECT_PUBLIC_KEY_INFO}`;var TBS_CERTIFICATE_ISSUER_UNIQUE_ID=`${TBS_CERTIFICATE}.${ISSUER_UNIQUE_ID}`;var TBS_CERTIFICATE_SUBJECT_UNIQUE_ID=`${TBS_CERTIFICATE}.${SUBJECT_UNIQUE_ID}`;var TBS_CERTIFICATE_EXTENSIONS=`${TBS_CERTIFICATE}.${EXTENSIONS$2}`;var CLEAR_PROPS$Q=[TBS_CERTIFICATE,TBS_CERTIFICATE_VERSION,TBS_CERTIFICATE_SERIAL_NUMBER,TBS_CERTIFICATE_SIGNATURE,TBS_CERTIFICATE_ISSUER,TBS_CERTIFICATE_NOT_BEFORE,TBS_CERTIFICATE_NOT_AFTER,TBS_CERTIFICATE_SUBJECT,TBS_CERTIFICATE_SUBJECT_PUBLIC_KEY,TBS_CERTIFICATE_ISSUER_UNIQUE_ID,TBS_CERTIFICATE_SUBJECT_UNIQUE_ID,TBS_CERTIFICATE_EXTENSIONS,SIGNATURE_ALGORITHM$5,SIGNATURE_VALUE$2];function tbsCertificate(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||TBS_CERTIFICATE,value:[new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:0},value:[new Integer({name:names.tbsCertificateVersion||TBS_CERTIFICATE_VERSION})]}),new Integer({name:names.tbsCertificateSerialNumber||TBS_CERTIFICATE_SERIAL_NUMBER}),AlgorithmIdentifier.schema(names.signature||{names:{blockName:TBS_CERTIFICATE_SIGNATURE}}),RelativeDistinguishedNames.schema(names.issuer||{names:{blockName:TBS_CERTIFICATE_ISSUER}}),new Sequence({name:names.tbsCertificateValidity||"tbsCertificate.validity",value:[Time.schema(names.notBefore||{names:{utcTimeName:TBS_CERTIFICATE_NOT_BEFORE,generalTimeName:TBS_CERTIFICATE_NOT_BEFORE}}),Time.schema(names.notAfter||{names:{utcTimeName:TBS_CERTIFICATE_NOT_AFTER,generalTimeName:TBS_CERTIFICATE_NOT_AFTER}})]}),RelativeDistinguishedNames.schema(names.subject||{names:{blockName:TBS_CERTIFICATE_SUBJECT}}),PublicKeyInfo.schema(names.subjectPublicKeyInfo||{names:{blockName:TBS_CERTIFICATE_SUBJECT_PUBLIC_KEY}}),new Primitive({name:names.tbsCertificateIssuerUniqueID||TBS_CERTIFICATE_ISSUER_UNIQUE_ID,optional:true,idBlock:{tagClass:3,tagNumber:1}}),new Primitive({name:names.tbsCertificateSubjectUniqueID||TBS_CERTIFICATE_SUBJECT_UNIQUE_ID,optional:true,idBlock:{tagClass:3,tagNumber:2}}),new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:3},value:[Extensions.schema(names.extensions||{names:{blockName:TBS_CERTIFICATE_EXTENSIONS}})]})]});}var Certificate=/*#__PURE__*/function(_PkiObject57){_inheritsLoose(Certificate,_PkiObject57);function Certificate(parameters){var _this82;if(parameters===void 0){parameters={};}_this82=_PkiObject57.call(this)||this;_this82.tbsView=new Uint8Array(getParametersValue(parameters,TBS$4,Certificate.defaultValues(TBS$4)));_this82.version=getParametersValue(parameters,VERSION$f,Certificate.defaultValues(VERSION$f));_this82.serialNumber=getParametersValue(parameters,SERIAL_NUMBER$3,Certificate.defaultValues(SERIAL_NUMBER$3));_this82.signature=getParametersValue(parameters,SIGNATURE$4,Certificate.defaultValues(SIGNATURE$4));_this82.issuer=getParametersValue(parameters,ISSUER$2,Certificate.defaultValues(ISSUER$2));_this82.notBefore=getParametersValue(parameters,NOT_BEFORE,Certificate.defaultValues(NOT_BEFORE));_this82.notAfter=getParametersValue(parameters,NOT_AFTER,Certificate.defaultValues(NOT_AFTER));_this82.subject=getParametersValue(parameters,SUBJECT$1,Certificate.defaultValues(SUBJECT$1));_this82.subjectPublicKeyInfo=getParametersValue(parameters,SUBJECT_PUBLIC_KEY_INFO,Certificate.defaultValues(SUBJECT_PUBLIC_KEY_INFO));if(ISSUER_UNIQUE_ID in parameters){_this82.issuerUniqueID=getParametersValue(parameters,ISSUER_UNIQUE_ID,Certificate.defaultValues(ISSUER_UNIQUE_ID));}if(SUBJECT_UNIQUE_ID in parameters){_this82.subjectUniqueID=getParametersValue(parameters,SUBJECT_UNIQUE_ID,Certificate.defaultValues(SUBJECT_UNIQUE_ID));}if(EXTENSIONS$2 in parameters){_this82.extensions=getParametersValue(parameters,EXTENSIONS$2,Certificate.defaultValues(EXTENSIONS$2));}_this82.signatureAlgorithm=getParametersValue(parameters,SIGNATURE_ALGORITHM$5,Certificate.defaultValues(SIGNATURE_ALGORITHM$5));_this82.signatureValue=getParametersValue(parameters,SIGNATURE_VALUE$2,Certificate.defaultValues(SIGNATURE_VALUE$2));if(parameters.schema){_this82.fromSchema(parameters.schema);}return _this82;}Certificate.defaultValues=function defaultValues(memberName){switch(memberName){case TBS$4:return EMPTY_BUFFER;case VERSION$f:return 0;case SERIAL_NUMBER$3:return new Integer();case SIGNATURE$4:return new AlgorithmIdentifier();case ISSUER$2:return new RelativeDistinguishedNames();case NOT_BEFORE:return new Time();case NOT_AFTER:return new Time();case SUBJECT$1:return new RelativeDistinguishedNames();case SUBJECT_PUBLIC_KEY_INFO:return new PublicKeyInfo();case ISSUER_UNIQUE_ID:return EMPTY_BUFFER;case SUBJECT_UNIQUE_ID:return EMPTY_BUFFER;case EXTENSIONS$2:return [];case SIGNATURE_ALGORITHM$5:return new AlgorithmIdentifier();case SIGNATURE_VALUE$2:return new BitString();default:return _PkiObject57.defaultValues.call(this,memberName);}};Certificate.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.blockName||EMPTY_STRING,value:[tbsCertificate(names.tbsCertificate),AlgorithmIdentifier.schema(names.signatureAlgorithm||{names:{blockName:SIGNATURE_ALGORITHM$5}}),new BitString({name:names.signatureValue||SIGNATURE_VALUE$2})]});};var _proto60=Certificate.prototype;_proto60.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$Q);var asn1=compareSchema(schema,schema,Certificate.schema({names:{tbsCertificate:{names:{extensions:{names:{extensions:TBS_CERTIFICATE_EXTENSIONS}}}}}}));AsnError.assertSchema(asn1,this.className);this.tbsView=asn1.result.tbsCertificate.valueBeforeDecodeView;if(TBS_CERTIFICATE_VERSION in asn1.result)this.version=asn1.result[TBS_CERTIFICATE_VERSION].valueBlock.valueDec;this.serialNumber=asn1.result[TBS_CERTIFICATE_SERIAL_NUMBER];this.signature=new AlgorithmIdentifier({schema:asn1.result[TBS_CERTIFICATE_SIGNATURE]});this.issuer=new RelativeDistinguishedNames({schema:asn1.result[TBS_CERTIFICATE_ISSUER]});this.notBefore=new Time({schema:asn1.result[TBS_CERTIFICATE_NOT_BEFORE]});this.notAfter=new Time({schema:asn1.result[TBS_CERTIFICATE_NOT_AFTER]});this.subject=new RelativeDistinguishedNames({schema:asn1.result[TBS_CERTIFICATE_SUBJECT]});this.subjectPublicKeyInfo=new PublicKeyInfo({schema:asn1.result[TBS_CERTIFICATE_SUBJECT_PUBLIC_KEY]});if(TBS_CERTIFICATE_ISSUER_UNIQUE_ID in asn1.result)this.issuerUniqueID=asn1.result[TBS_CERTIFICATE_ISSUER_UNIQUE_ID].valueBlock.valueHex;if(TBS_CERTIFICATE_SUBJECT_UNIQUE_ID in asn1.result)this.subjectUniqueID=asn1.result[TBS_CERTIFICATE_SUBJECT_UNIQUE_ID].valueBlock.valueHex;if(TBS_CERTIFICATE_EXTENSIONS in asn1.result)this.extensions=Array.from(asn1.result[TBS_CERTIFICATE_EXTENSIONS],element=>new Extension({schema:element}));this.signatureAlgorithm=new AlgorithmIdentifier({schema:asn1.result.signatureAlgorithm});this.signatureValue=asn1.result.signatureValue;};_proto60.encodeTBS=function encodeTBS(){var outputArray=[];if(VERSION$f in this&&this.version!==Certificate.defaultValues(VERSION$f)){outputArray.push(new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:0},value:[new Integer({value:this.version})]}));}outputArray.push(this.serialNumber);outputArray.push(this.signature.toSchema());outputArray.push(this.issuer.toSchema());outputArray.push(new Sequence({value:[this.notBefore.toSchema(),this.notAfter.toSchema()]}));outputArray.push(this.subject.toSchema());outputArray.push(this.subjectPublicKeyInfo.toSchema());if(this.issuerUniqueID){outputArray.push(new Primitive({optional:true,idBlock:{tagClass:3,tagNumber:1},valueHex:this.issuerUniqueID}));}if(this.subjectUniqueID){outputArray.push(new Primitive({optional:true,idBlock:{tagClass:3,tagNumber:2},valueHex:this.subjectUniqueID}));}if(this.extensions){outputArray.push(new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:3},value:[new Sequence({value:Array.from(this.extensions,o=>o.toSchema())})]}));}return new Sequence({value:outputArray});};_proto60.toSchema=function toSchema(encodeFlag){if(encodeFlag===void 0){encodeFlag=false;}var tbsSchema;if(encodeFlag===false){if(!this.tbsView.byteLength){return Certificate.schema().value[0];}var asn1=fromBER(this.tbsView);AsnError.assert(asn1,"TBS Certificate");tbsSchema=asn1.result;}else {tbsSchema=this.encodeTBS();}return new Sequence({value:[tbsSchema,this.signatureAlgorithm.toSchema(),this.signatureValue]});};_proto60.toJSON=function toJSON(){var res={tbs:Convert.ToHex(this.tbsView),version:this.version,serialNumber:this.serialNumber.toJSON(),signature:this.signature.toJSON(),issuer:this.issuer.toJSON(),notBefore:this.notBefore.toJSON(),notAfter:this.notAfter.toJSON(),subject:this.subject.toJSON(),subjectPublicKeyInfo:this.subjectPublicKeyInfo.toJSON(),signatureAlgorithm:this.signatureAlgorithm.toJSON(),signatureValue:this.signatureValue.toJSON()};if(VERSION$f in this&&this.version!==Certificate.defaultValues(VERSION$f)){res.version=this.version;}if(this.issuerUniqueID){res.issuerUniqueID=Convert.ToHex(this.issuerUniqueID);}if(this.subjectUniqueID){res.subjectUniqueID=Convert.ToHex(this.subjectUniqueID);}if(this.extensions){res.extensions=Array.from(this.extensions,o=>o.toJSON());}return res;};_proto60.getPublicKey=function getPublicKey(parameters,crypto){try{var _this83=this;if(crypto===void 0){crypto=getCrypto(true);}return _await(crypto.getPublicKey(_this83.subjectPublicKeyInfo,_this83.signatureAlgorithm,parameters));}catch(e){return Promise.reject(e);}};_proto60.getKeyHash=function getKeyHash(hashAlgorithm,crypto){try{var _this84=this;if(hashAlgorithm===void 0){hashAlgorithm="SHA-1";}if(crypto===void 0){crypto=getCrypto(true);}return _await(crypto.digest({name:hashAlgorithm},_this84.subjectPublicKeyInfo.subjectPublicKey.valueBlock.valueHexView));}catch(e){return Promise.reject(e);}};_proto60.sign=function sign(privateKey,hashAlgorithm,crypto){try{var _this85=this;if(hashAlgorithm===void 0){hashAlgorithm="SHA-1";}if(crypto===void 0){crypto=getCrypto(true);}if(!privateKey){throw new Error("Need to provide a private key for signing");}return _await(crypto.getSignatureParameters(privateKey,hashAlgorithm),signatureParameters=>{var parameters=signatureParameters.parameters;_this85.signature=signatureParameters.signatureAlgorithm;_this85.signatureAlgorithm=signatureParameters.signatureAlgorithm;_this85.tbsView=new Uint8Array(_this85.encodeTBS().toBER());return _await(crypto.signWithPrivateKey(_this85.tbsView,privateKey,parameters),signature=>{_this85.signatureValue=new BitString({valueHex:signature});});});}catch(e){return Promise.reject(e);}};_proto60.verify=function verify(issuerCertificate,crypto){try{var _this86=this;if(crypto===void 0){crypto=getCrypto(true);}var subjectPublicKeyInfo;if(issuerCertificate){subjectPublicKeyInfo=issuerCertificate.subjectPublicKeyInfo;}else if(_this86.issuer.isEqual(_this86.subject)){subjectPublicKeyInfo=_this86.subjectPublicKeyInfo;}if(!(subjectPublicKeyInfo instanceof PublicKeyInfo)){throw new Error("Please provide issuer certificate as a parameter");}return _await(crypto.verifyWithPublicKey(_this86.tbsView,_this86.signatureValue,subjectPublicKeyInfo,_this86.signatureAlgorithm));}catch(e){return Promise.reject(e);}};_createClass(Certificate,[{key:"tbs",get:function(){return BufferSourceConverter.toArrayBuffer(this.tbsView);},set:function(value){this.tbsView=new Uint8Array(value);}}]);return Certificate;}(PkiObject);Certificate.CLASS_NAME="Certificate";var ChainValidationCode;(function(ChainValidationCode){ChainValidationCode[ChainValidationCode["unknown"]=-1]="unknown";ChainValidationCode[ChainValidationCode["success"]=0]="success";ChainValidationCode[ChainValidationCode["noRevocation"]=11]="noRevocation";ChainValidationCode[ChainValidationCode["noPath"]=60]="noPath";ChainValidationCode[ChainValidationCode["noValidPath"]=97]="noValidPath";})(ChainValidationCode||(ChainValidationCode={}));var TBS$1="tbs";var VERSION$6="version";var SUBJECT="subject";var SPKI="subjectPublicKeyInfo";var ATTRIBUTES$1="attributes";var SIGNATURE_ALGORITHM$2="signatureAlgorithm";var SIGNATURE_VALUE="signatureValue";var CSR_INFO="CertificationRequestInfo";var CSR_INFO_VERSION=`${CSR_INFO}.version`;var CSR_INFO_SUBJECT=`${CSR_INFO}.subject`;var CSR_INFO_SPKI=`${CSR_INFO}.subjectPublicKeyInfo`;var CSR_INFO_ATTRS=`${CSR_INFO}.attributes`;var CLEAR_PROPS$f=[CSR_INFO,CSR_INFO_VERSION,CSR_INFO_SUBJECT,CSR_INFO_SPKI,CSR_INFO_ATTRS,SIGNATURE_ALGORITHM$2,SIGNATURE_VALUE];function CertificationRequestInfo(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({name:names.CertificationRequestInfo||CSR_INFO,value:[new Integer({name:names.CertificationRequestInfoVersion||CSR_INFO_VERSION}),RelativeDistinguishedNames.schema(names.subject||{names:{blockName:CSR_INFO_SUBJECT}}),PublicKeyInfo.schema({names:{blockName:CSR_INFO_SPKI}}),new Constructed({optional:true,idBlock:{tagClass:3,tagNumber:0},value:[new Repeated({optional:true,name:names.CertificationRequestInfoAttributes||CSR_INFO_ATTRS,value:Attribute.schema(names.attributes||{})})]})]});}var CertificationRequest=/*#__PURE__*/function(_PkiObject96){_inheritsLoose(CertificationRequest,_PkiObject96);function CertificationRequest(parameters){var _this142;if(parameters===void 0){parameters={};}_this142=_PkiObject96.call(this)||this;_this142.tbsView=new Uint8Array(getParametersValue(parameters,TBS$1,CertificationRequest.defaultValues(TBS$1)));_this142.version=getParametersValue(parameters,VERSION$6,CertificationRequest.defaultValues(VERSION$6));_this142.subject=getParametersValue(parameters,SUBJECT,CertificationRequest.defaultValues(SUBJECT));_this142.subjectPublicKeyInfo=getParametersValue(parameters,SPKI,CertificationRequest.defaultValues(SPKI));if(ATTRIBUTES$1 in parameters){_this142.attributes=getParametersValue(parameters,ATTRIBUTES$1,CertificationRequest.defaultValues(ATTRIBUTES$1));}_this142.signatureAlgorithm=getParametersValue(parameters,SIGNATURE_ALGORITHM$2,CertificationRequest.defaultValues(SIGNATURE_ALGORITHM$2));_this142.signatureValue=getParametersValue(parameters,SIGNATURE_VALUE,CertificationRequest.defaultValues(SIGNATURE_VALUE));if(parameters.schema){_this142.fromSchema(parameters.schema);}return _this142;}CertificationRequest.defaultValues=function defaultValues(memberName){switch(memberName){case TBS$1:return EMPTY_BUFFER;case VERSION$6:return 0;case SUBJECT:return new RelativeDistinguishedNames();case SPKI:return new PublicKeyInfo();case ATTRIBUTES$1:return [];case SIGNATURE_ALGORITHM$2:return new AlgorithmIdentifier();case SIGNATURE_VALUE:return new BitString();default:return _PkiObject96.defaultValues.call(this,memberName);}};CertificationRequest.schema=function schema(parameters){if(parameters===void 0){parameters={};}var names=getParametersValue(parameters,"names",{});return new Sequence({value:[CertificationRequestInfo(names.certificationRequestInfo||{}),new Sequence({name:names.signatureAlgorithm||SIGNATURE_ALGORITHM$2,value:[new ObjectIdentifier(),new Any({optional:true})]}),new BitString({name:names.signatureValue||SIGNATURE_VALUE})]});};var _proto100=CertificationRequest.prototype;_proto100.fromSchema=function fromSchema(schema){clearProps(schema,CLEAR_PROPS$f);var asn1=compareSchema(schema,schema,CertificationRequest.schema());AsnError.assertSchema(asn1,this.className);this.tbsView=asn1.result.CertificationRequestInfo.valueBeforeDecodeView;this.version=asn1.result[CSR_INFO_VERSION].valueBlock.valueDec;this.subject=new RelativeDistinguishedNames({schema:asn1.result[CSR_INFO_SUBJECT]});this.subjectPublicKeyInfo=new PublicKeyInfo({schema:asn1.result[CSR_INFO_SPKI]});if(CSR_INFO_ATTRS in asn1.result){this.attributes=Array.from(asn1.result[CSR_INFO_ATTRS],element=>new Attribute({schema:element}));}this.signatureAlgorithm=new AlgorithmIdentifier({schema:asn1.result.signatureAlgorithm});this.signatureValue=asn1.result.signatureValue;};_proto100.encodeTBS=function encodeTBS(){var outputArray=[new Integer({value:this.version}),this.subject.toSchema(),this.subjectPublicKeyInfo.toSchema()];if(ATTRIBUTES$1 in this){outputArray.push(new Constructed({idBlock:{tagClass:3,tagNumber:0},value:Array.from(this.attributes||[],o=>o.toSchema())}));}return new Sequence({value:outputArray});};_proto100.toSchema=function toSchema(encodeFlag){if(encodeFlag===void 0){encodeFlag=false;}var tbsSchema;if(encodeFlag===false){if(this.tbsView.byteLength===0){return CertificationRequest.schema();}var asn1=fromBER(this.tbsView);AsnError.assert(asn1,"PKCS#10 Certificate Request");tbsSchema=asn1.result;}else {tbsSchema=this.encodeTBS();}return new Sequence({value:[tbsSchema,this.signatureAlgorithm.toSchema(),this.signatureValue]});};_proto100.toJSON=function toJSON(){var object={tbs:Convert.ToHex(this.tbsView),version:this.version,subject:this.subject.toJSON(),subjectPublicKeyInfo:this.subjectPublicKeyInfo.toJSON(),signatureAlgorithm:this.signatureAlgorithm.toJSON(),signatureValue:this.signatureValue.toJSON()};if(ATTRIBUTES$1 in this){object.attributes=Array.from(this.attributes||[],o=>o.toJSON());}return object;};_proto100.sign=function sign(privateKey,hashAlgorithm,crypto){try{var _this143=this;if(hashAlgorithm===void 0){hashAlgorithm="SHA-1";}if(crypto===void 0){crypto=getCrypto(true);}if(!privateKey){throw new Error("Need to provide a private key for signing");}return _await(crypto.getSignatureParameters(privateKey,hashAlgorithm),signatureParams=>{var parameters=signatureParams.parameters;_this143.signatureAlgorithm=signatureParams.signatureAlgorithm;_this143.tbsView=new Uint8Array(_this143.encodeTBS().toBER());return _await(crypto.signWithPrivateKey(_this143.tbsView,privateKey,parameters),signature=>{_this143.signatureValue=new BitString({valueHex:signature});});});}catch(e){return Promise.reject(e);}};_proto100.verify=function verify(crypto){try{var _this144=this;if(crypto===void 0){crypto=getCrypto(true);}return _await(crypto.verifyWithPublicKey(_this144.tbsView,_this144.signatureValue,_this144.subjectPublicKeyInfo,_this144.signatureAlgorithm));}catch(e){return Promise.reject(e);}};_proto100.getPublicKey=function getPublicKey(parameters,crypto){try{var _this145=this;if(crypto===void 0){crypto=getCrypto(true);}return _await(crypto.getPublicKey(_this145.subjectPublicKeyInfo,_this145.signatureAlgorithm,parameters));}catch(e){return Promise.reject(e);}};_createClass(CertificationRequest,[{key:"tbs",get:function(){return BufferSourceConverter.toArrayBuffer(this.tbsView);},set:function(value){this.tbsView=new Uint8Array(value);}}]);return CertificationRequest;}(PkiObject);CertificationRequest.CLASS_NAME="CertificationRequest";var PKIStatus;(function(PKIStatus){PKIStatus[PKIStatus["granted"]=0]="granted";PKIStatus[PKIStatus["grantedWithMods"]=1]="grantedWithMods";PKIStatus[PKIStatus["rejection"]=2]="rejection";PKIStatus[PKIStatus["waiting"]=3]="waiting";PKIStatus[PKIStatus["revocationWarning"]=4]="revocationWarning";PKIStatus[PKIStatus["revocationNotification"]=5]="revocationNotification";})(PKIStatus||(PKIStatus={}));function initCryptoEngine(){if(typeof self!=="undefined"){if("crypto"in self){var engineName="webcrypto";if("webkitSubtle"in self.crypto){engineName="safari";}setEngine(engineName,new CryptoEngine({name:engineName,crypto:crypto}));}}else if(typeof crypto!=="undefined"&&"webcrypto"in crypto){var name="NodeJS ^15";var nodeCrypto=crypto.webcrypto;setEngine(name,new CryptoEngine({name,crypto:nodeCrypto}));}}initCryptoEngine();

var LogLevel = /*#__PURE__*/function (LogLevel) {
  LogLevel[LogLevel["Debug"] = 1] = "Debug";
  LogLevel[LogLevel["Info"] = 2] = "Info";
  LogLevel[LogLevel["Warn"] = 3] = "Warn";
  LogLevel[LogLevel["Error"] = 4] = "Error";
  return LogLevel;
}({});

/** what Logger needs from the global ngx */

/**
 * Logger is a leveled logger on top of ngx.log that adds a consistent
 * prefix to log messages.
 *
 * @example
 * const log = new Logger('my module')
 * log.info('foo')
 * // equivalent to `ngx.log(ngx.INFO, 'njs-acme: [my module] foo')`
 *
 * log.debug('bar') // does nothing by default
 * log.minLevel = LogLevel.Debug // enabling more verbosity
 *
 * log.debug('bar')
 * // now equivalent to `ngx.log(ngx.INFO, 'njs-acme: [my module] bar')`
 *
 * // multiple args are stringified and joined on space:
 * log.info('baz:', true, {key: "value"})
 * // equivalent to `ngx.log(ngx.INFO, 'njs-acme: [my module] baz: true {"key":"value"}')`
 */
var Logger = /*#__PURE__*/function () {
  /**
   * @param module preprended to every log message, if non-empty
   * @param minLevel lowest level to log, anything below will be ignored
   * @param ngx log sink, intended for testing purposes
   */
  function Logger(module, minLevel, base) {
    if (module === void 0) {
      module = '';
    }
    if (minLevel === void 0) {
      minLevel = LogLevel.Info;
    }
    this.prefix = void 0;
    this.logLevelMap = void 0;
    this.ngx = void 0;
    this.minLevel = minLevel;
    // the global `ngx` object is late bound, and undefined if we use it as a
    // default parameter
    this.ngx = base ?? ngx;
    this.prefix = module ? `njs-acme: [${module}]` : 'njs-acme:';
    this.logLevelMap = {
      [LogLevel.Debug]: this.ngx.INFO,
      [LogLevel.Info]: this.ngx.INFO,
      [LogLevel.Warn]: this.ngx.WARN,
      [LogLevel.Error]: this.ngx.ERR
    };
  }
  var _proto = Logger.prototype;
  _proto.log = function log(level, args) {
    if (args.length === 0) {
      return;
    }
    if (level < this.minLevel) {
      return;
    }
    var message = [this.prefix].concat(args).map(a => typeof a === 'string' ? a : JSON.stringify(a)).join(' ');
    this.ngx.log(this.logLevelMap[level], message);
  }

  /**
   * debug is a synthetic log level to control verbosity, use this for logs that
   * are useful only during the development process.
   *
   * Will appear in logs as ngx.INFO.
   * */;
  _proto.debug = function debug() {
    for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }
    this.log(LogLevel.Debug, args);
  };
  _proto.info = function info() {
    for (var _len2 = arguments.length, args = new Array(_len2), _key2 = 0; _key2 < _len2; _key2++) {
      args[_key2] = arguments[_key2];
    }
    this.log(LogLevel.Info, args);
  };
  _proto.warn = function warn() {
    for (var _len3 = arguments.length, args = new Array(_len3), _key3 = 0; _key3 < _len3; _key3++) {
      args[_key3] = arguments[_key3];
    }
    this.log(LogLevel.Warn, args);
  };
  _proto.error = function error() {
    for (var _len4 = arguments.length, args = new Array(_len4), _key4 = 0; _key4 < _len4; _key4++) {
      args[_key4] = arguments[_key4];
    }
    this.log(LogLevel.Error, args);
  };
  return Logger;
}();

/**
 * Read information from a certificate
 * If multiple certificates are chained, the first will be read
 *
 * @param {buffer|string} certPem PEM encoded certificate or chain
 * @returns {CertificateInfo} Certificate info
 */
var readCertificateInfo = _async(certPem => {
  var certBuffer = pemToBuffer(certPem, 'CERTIFICATE');
  var cert = Certificate.fromBER(certBuffer);
  var issuer = cert.issuer.typesAndValues.map(typeAndValue => ({
    [typeAndValue.type]: typeAndValue.value.valueBlock.value
  }));
  return {
    issuer,
    domains: readX509ServerNames(certPem),
    notBefore: cert.notBefore.value,
    notAfter: cert.notAfter.value
  };
});

/**
 * Converts a PEM encoded string to a Buffer.
 * @param {string} pem Pem encoded input
 * @param {string} tag The tag name used to identify the PEM block.
 * @returns Buffer
 */
/**
 * Retry promise
 *
 * @param {function} fn Function returning promise that should be retried
 * @param {number} attempts Maximum number of attempts
 * @param {Backoff} backoff Backoff instance
 * @returns {Promise}
 */
var retryPromise = _async((fn, attempts, backoff) => {
  var aborted = false;
  return _catch(() => _await(fn(() => {
    aborted = true;
  })), e => {
    if (aborted || backoff.attempts + 1 >= attempts) {
      throw e;
    }
    var duration = backoff.duration();
    log$1.info(`Promise rejected attempt #${backoff.attempts}, retrying in ${duration}ms: ${e}`);
    return _await(new Promise(resolve => {
      setTimeout(resolve, duration, {});
    }), () => retryPromise(fn, attempts, backoff));
  });
});
/**
 * Retry promise
 *
 * @param {function} fn Function returning promise that should be retried
 * @param {object} [backoffOpts] Backoff options
 * @param {number} [backoffOpts.attempts] Maximum number of attempts, default: `5`
 * @param {number} [backoffOpts.min] Minimum attempt delay in milliseconds, default: `5000`
 * @param {number} [backoffOpts.max] Maximum attempt delay in milliseconds, default: `30000`
 * @returns {Promise}
 */
var signCsr = _async((pkcs10, privateKey) => {
  /* Set signatureValue  */
  pkcs10.tbsView = new Uint8Array(encodeTBS(pkcs10).toBER());
  return _await(crypto.subtle.sign('RSASSA-PKCS1-v1_5', privateKey, pkcs10.tbsView), signature => {
    pkcs10.signatureValue = new BitString({
      valueHex: signature
    });

    /* Set signatureAlgorithm */
    var signatureParams = getSignatureParameters(privateKey, 'SHA-256');
    pkcs10.signatureAlgorithm = signatureParams.signatureAlgorithm;
  });
});
var getSubjectKeyIdentifier = _async(pkcs10 => {
  var subjectPublicKeyValue = pkcs10.subjectPublicKeyInfo.subjectPublicKey.valueBlock.valueHex;
  return _await(crypto.subtle.digest('SHA-256', subjectPublicKeyValue), subjectKeyIdentifier => new OctetString({
    valueHex: subjectKeyIdentifier
  }));
});
var addExtensions = _async((pkcs10, params, publicKey) => _await(pkcs10.subjectPublicKeyInfo.importKey(publicKey, getCrypto(true)), () => _await(getSubjectKeyIdentifier(pkcs10), subjectKeyIdentifier => {
  // Note that the set of AltNames must also include the commonName.
  var serverNamesGNs = new GeneralNames({
    names: getServerNamesAsGeneralNames(params)
  });
  var extensions = new Extensions({
    extensions: [createExtension('2.5.29.14', subjectKeyIdentifier),
    // SubjectKeyIdentifier
    createExtension('2.5.29.17', serverNamesGNs.toSchema()) // SubjectAltName
    ]
  });

  pkcs10.attributes = [];
  pkcs10.attributes.push(new Attribute({
    type: '1.2.840.113549.1.9.14',
    // pkcs-9-at-extensionRequest
    values: [extensions.toSchema()]
  }));
})));
/**
 * Create a Certificate Signing Request
 *
 * @param {object} params - CSR parameters
 * @param {number} [params.keySize] - Size of the newly created private key, default: `2048`
 * @param {string} [params.commonName] - Common name
 * @param {string[]} [params.altNames] - Alternative names, default: `[]`
 * @param {string} [params.country] - Country name
 * @param {string} [params.state] - State or province name
 * @param {string} [params.locality] - Locality or city name
 * @param {string} [params.organization] - Organization name
 * @param {string} [params.organizationUnit] - Organization unit name
 * @param {string} [params.emailAddress] - Email address
 * @returns {Promise<{ pkcs10Ber: ArrayBuffer; keys: Required<CryptoKeyPair> }>} - Object containing
 * the PKCS10 BER representation and generated keys
 */
var createCsr = params => _call(generateKey, _generateKey2 => {
  var _ref = _generateKey2,
    privateKey = _ref.privateKey,
    publicKey = _ref.publicKey;
  var pkcs10 = new CertificationRequest();
  pkcs10.version = 0;
  addSubjectAttributes(pkcs10.subject.typesAndValues, params);
  return _await(addExtensions(pkcs10, params, publicKey), () => _await(signCsr(pkcs10, privateKey), () => {
    var pkcs10Ber = getPkcs10Ber(pkcs10);
    return {
      pkcs10Ber,
      keys: {
        privateKey,
        publicKey
      }
    };
  }));
});
/**
 * Gets the public JWK from a given private key.
 * @param {CryptoKey} privateKey - The private key to extract the public JWK from.
 * @returns {Promise<RsaPublicJwk | EcdsaPublicJwk>} The public JWK.
 * @throws {Error} Throws an error if the privateKey parameter is not provided or invalid.
 */
var getPublicJwk = _async(privateKey => {
  if (!privateKey) {
    var errMsg = 'Invalid or missing private key';
    log$1.error(errMsg);
    throw new Error(errMsg);
  }

  // eslint-disable-next-line @typescript-eslint/ban-types
  return _await(crypto.subtle.exportKey('jwk', privateKey), _crypto$subtle$export => {
    var jwk = _crypto$subtle$export;
    if (jwk.crv && jwk.kty === 'EC') {
      var crv = jwk.crv,
        _x = jwk.x,
        y = jwk.y,
        kty = jwk.kty;
      return {
        crv,
        kty,
        x: _x,
        y
      };
    } else {
      return {
        e: jwk.e,
        kty: jwk.kty,
        n: jwk.n
      };
    }
  });
});

/**
 * Add line break every 64th character
 * @param pemString {string}
 * @returns  {string}
 */
/**
 * Reads the account key from the specified file path, or creates a new one if it does not exist.
 * @param {string} [path] - The path to the account key file. If not specified, the default location will be used.
 * @returns {Promise<CryptoKey>} - The account key as a CryptoKey object.
 * @throws {Error} - If the account key cannot be read or generated.
 */
var readOrCreateAccountKey = _async(path => _catch(() => {
  var accountKeyJWK = fs.readFileSync(path, 'utf8');
  log$1.info('Using account key from', path);
  return _await(crypto.subtle.importKey('jwk', JSON.parse(accountKeyJWK), ACCOUNT_KEY_ALG_IMPORT, true, ['sign']));
}, e => {
  // TODO: separate file not found, issues with importKey
  log$1.warn(`error ${e} while reading a private key from ${path}`);

  /* Generate a new RSA key pair for ACME account */
  return _call(generateKey, _generateKey => {
    var keys = _generateKey;
    return _await(crypto.subtle.exportKey('jwk', keys.privateKey), jwkFormated => {
      fs.writeFileSync(path, JSON.stringify(jwkFormated));
      log$1.info('Generated a new account key and saved it to', path);
      return keys.privateKey;
    });
  });
}));
/**
 * Generates RSA private and public key pair
 * @returns {CryptoKeyPair} a private and public key pair
 */
var generateKey = _async(() => crypto.subtle.generateKey(ACCOUNT_KEY_ALG_GENERATE, true, ['sign', 'verify']));
var log$1 = new Logger('utils');

// workaround for PKI.JS to work
globalThis.unescape = querystring.unescape;

// make PKI.JS to work with webcrypto
setEngine('webcrypto', new CryptoEngine({
  name: 'webcrypto',
  crypto: crypto
}));
var ACCOUNT_KEY_ALG_GENERATE = {
  name: 'RSASSA-PKCS1-v1_5',
  hash: 'SHA-256',
  publicExponent: new Uint8Array([1, 0, 1]),
  modulusLength: 2048
};
var ACCOUNT_KEY_ALG_IMPORT = {
  name: 'RSASSA-PKCS1-v1_5',
  hash: 'SHA-256'
};
function formatPEM(pemString) {
  return pemString.replace(/(.{64})/g, '$1\n');
}
/**
 * Convert ArrayBufferView | ArrayBuffer to PEM string
 * @param buffer The ArrayBufferView | ArrayBuffer to convert to PEM
 * @param tag The tag to use for the PEM header and footer
 * @returns The converted PEM string
 */
function toPEM(buffer, tag) {
  /**
   * Convert the ArrayBufferView or ArrayBuffer to base64 and format it
   * as a PEM string
   */
  var pemBody = formatPEM(Buffer.from(buffer).toString('base64'));

  // Construct and return the final PEM string
  return [`-----BEGIN ${tag}-----`, pemBody, `-----END ${tag}-----`, ''].join('\n');
}

/**
 * Encodes a PKCS#10 certification request into an ASN.1 TBS (To-Be-Signed) sequence.
 *
 * @param pkcs10 The PKCS#10 certification request object to encode.
 * @returns An ASN.1 sequence object representing the TBS.
 */
function encodeTBS(pkcs10) {
  var outputArray = [new Integer({
    value: pkcs10.version
  }), pkcs10.subject.toSchema(), pkcs10.subjectPublicKeyInfo.toSchema()];
  if (pkcs10.attributes !== undefined) {
    outputArray.push(new Constructed({
      idBlock: {
        tagClass: 3,
        // CONTEXT-SPECIFIC
        tagNumber: 0 // [0]
      },

      value: Array.from(pkcs10.attributes, o => o.toSchema())
    }));
  }
  return new Sequence({
    value: outputArray
  });
}

/**
 * Returns signature parameters based on the private key and hash algorithm
 *
 * @param privateKey {CryptoKey} The private key used for the signature
 * @param hashAlgorithm {string} The hash algorithm used for the signature. Default is "SHA-1".
 * @returns {{signatureAlgorithm: pkijs.AlgorithmIdentifier; parameters: pkijs.CryptoEngineAlgorithmParams;}} An object containing signature algorithm and parameters
 */
function getSignatureParameters(privateKey, hashAlgorithm) {
  if (hashAlgorithm === void 0) {
    hashAlgorithm = 'SHA-1';
  }
  // Check hashing algorithm
  getOIDByAlgorithm({
    name: hashAlgorithm
  }, true, 'hashAlgorithm');
  // Initial variables
  var signatureAlgorithm = new AlgorithmIdentifier();

  //#region Get a "default parameters" for current algorithm
  var parameters = getAlgorithmParameters(privateKey.algorithm.name, 'sign');
  if (!Object.keys(parameters.algorithm).length) {
    var errMsg = 'Parameter `algorithm` is empty';
    log$1.error(errMsg);
    throw new Error(errMsg);
  }
  var algorithm = parameters.algorithm;
  algorithm.hash.name = hashAlgorithm;
  //#endregion

  //#region Fill internal structures base on "privateKey" and "hashAlgorithm"
  switch (privateKey.algorithm.name.toUpperCase()) {
    case 'RSASSA-PKCS1-V1_5':
    case 'ECDSA':
      signatureAlgorithm.algorithmId = getOIDByAlgorithm(algorithm, true);
      break;
    case 'RSA-PSS':
      {
        //#region Set "saltLength" as a length (in octets) of hash function result
        switch (hashAlgorithm.toUpperCase()) {
          case 'SHA-256':
            algorithm.saltLength = 32;
            break;
          case 'SHA-384':
            algorithm.saltLength = 48;
            break;
          case 'SHA-512':
            algorithm.saltLength = 64;
            break;
        }
        //#endregion

        //#region Fill "RSASSA_PSS_params" object
        var paramsObject = {};
        if (hashAlgorithm.toUpperCase() !== 'SHA-1') {
          var hashAlgorithmOID = getOIDByAlgorithm({
            name: hashAlgorithm
          }, true, 'hashAlgorithm');
          paramsObject.hashAlgorithm = new AlgorithmIdentifier({
            algorithmId: hashAlgorithmOID,
            algorithmParams: new Null()
          });
          paramsObject.maskGenAlgorithm = new AlgorithmIdentifier({
            algorithmId: '1.2.840.113549.1.1.8',
            // MGF1
            algorithmParams: paramsObject.hashAlgorithm.toSchema()
          });
        }
        if (algorithm.saltLength !== 20) paramsObject.saltLength = algorithm.saltLength;
        var pssParameters = new RSASSAPSSParams(paramsObject);
        //#endregion

        //#region Automatically set signature algorithm
        signatureAlgorithm.algorithmId = '1.2.840.113549.1.1.10';
        signatureAlgorithm.algorithmParams = pssParameters.toSchema();
        //#endregion
      }

      break;
    default:
      log$1.error(`Unsupported signature algorithm: ${privateKey.algorithm.name}`);
      throw new Error(`Unsupported signature algorithm: ${privateKey.algorithm.name}`);
  }
  //#endregion

  return {
    signatureAlgorithm,
    parameters
  };
}
function addSubjectAttributes(subjectTypesAndValues, params) {
  if (params.country) {
    subjectTypesAndValues.push(createAttributeTypeAndValue('2.5.4.6', params.country));
  }
  if (params.state) {
    subjectTypesAndValues.push(createAttributeTypeAndValue('2.5.4.8', params.state));
  }
  if (params.organization) {
    subjectTypesAndValues.push(createAttributeTypeAndValue('2.5.4.10', params.organization));
  }
  if (params.organizationUnit) {
    subjectTypesAndValues.push(createAttributeTypeAndValue('2.5.4.11', params.organizationUnit));
  }
  if (params.commonName) {
    subjectTypesAndValues.push(createAttributeTypeAndValue('2.5.4.3', params.commonName));
  }
}
function createAttributeTypeAndValue(type, value) {
  return new AttributeTypeAndValue({
    type,
    value: new Utf8String({
      value
    })
  });
}
function getServerNamesAsGeneralNames(params) {
  var altNames = [];

  // add common name first so that it becomes the cert common name
  if (params.commonName && !altNames.some(name => name.toString() === params.commonName)) {
    altNames.push(createGeneralName(2, params.commonName));
  }

  // altNames follow common name
  if (params.altNames) {
    altNames.push.apply(altNames, params.altNames.map(altName => createGeneralName(2, altName)));
  }
  return altNames;
}
function createGeneralName(type, value) {
  return new GeneralName({
    type,
    value
  });
}
function createExtension(extnID, extnValue) {
  return new Extension({
    extnID,
    critical: false,
    extnValue: extnValue.toBER(false)
  });
}
function getPkcs10Ber(pkcs10) {
  return pkcs10.toSchema(true).toBER(false);
}

/**
 * Returns the Base64url encoded representation of the input data.
 *
 * @param {string} data - The data to be encoded.
 * @returns {string} - The Base64url encoded representation of the input data.
 */
function getPemBodyAsB64u(data) {
  var buf = data;
  if (typeof data === 'string') {
    buf = Buffer.from(data);
  }
  return buf.toString('base64url');
}

/**
 * Find and format error in response object
 *
 * @param {object} resp HTTP response
 * @returns {string} Error message
 */
// eslint-disable-next-line @typescript-eslint/explicit-module-boundary-types, @typescript-eslint/no-explicit-any
function formatResponseError(data) {
  var result;
  // const data = await resp.json();
  if ('error' in data) {
    result = data.error.detail || data.error;
  } else {
    result = data.detail || JSON.stringify(data);
  }
  return result.replace(/\n/g, '');
}

/**
 * Exponential backoff
 *
 * https://github.com/mokesmokes/backo
 *
 * @class
 * @param {object} [opts]
 * @param {number} [opts.min] Minimum backoff duration in ms
 * @param {number} [opts.max] Maximum backoff duration in ms
 */
var Backoff = /*#__PURE__*/function () {
  function Backoff(_temp) {
    var _ref2 = _temp === void 0 ? {} : _temp,
      _ref2$min = _ref2.min,
      min = _ref2$min === void 0 ? 100 : _ref2$min,
      _ref2$max = _ref2.max,
      max = _ref2$max === void 0 ? 10000 : _ref2$max;
    this.min = void 0;
    this.max = void 0;
    this.attempts = void 0;
    this.min = min;
    this.max = max;
    this.attempts = 0;
  }

  /**
   * Get backoff duration
   *
   * @returns {number} Backoff duration in ms
   */
  var _proto = Backoff.prototype;
  _proto.duration = function duration() {
    var ms = this.min * 2 ** this.attempts;
    this.attempts += 1;
    return Math.min(ms, this.max);
  };
  return Backoff;
}();
function retry(fn, _temp2) {
  var _ref3 = _temp2 === void 0 ? {} : _temp2,
    _ref3$attempts = _ref3.attempts,
    attempts = _ref3$attempts === void 0 ? 5 : _ref3$attempts,
    _ref3$min = _ref3.min,
    min = _ref3$min === void 0 ? 5000 : _ref3$min,
    _ref3$max = _ref3.max,
    max = _ref3$max === void 0 ? 30000 : _ref3$max;
  var backoff = new Backoff({
    min,
    max
  });
  return retryPromise(fn, attempts, backoff);
}
function pemToBuffer(pem, tag) {
  if (tag === void 0) {
    tag = 'PRIVATE KEY';
  }
  return Buffer.from(pem.replace(new RegExp(`(-----BEGIN ${tag}-----|-----END ${tag}-----|\n)`, 'g'), ''), 'base64');
}
/**
 * Given a `domains` object, which follows the format returned by readX509ServerNames(),
 * returns
 * @param domains CertDomains
 */
function uniqueDomains(domains) {
  var uniqueDomains = [domains.commonName];
  for (var _i2 = 0, _domains$altNames2 = domains.altNames; _i2 < _domains$altNames2.length; _i2++) {
    var altName = _domains$altNames2[_i2];
    if (uniqueDomains.indexOf(altName) === -1) {
      uniqueDomains.push(altName);
    }
  }
  return uniqueDomains;
}

/**
 * Reads the common name and alternative names from a PEM-formatted cert or CSR
 * (Certificate Signing Request).
 * @param certPem The PEM-encoded cert or CSR string or a Buffer containing the same.
 * @returns An object with the commonName and altNames extracted from the cert/CSR.
 *          If the cert does not have alternative names, altNames will be empty.
 */
function readX509ServerNames(certPem) {
  if (Buffer.isBuffer(certPem)) {
    certPem = certPem.toString();
  }
  var csr = x509.parse_pem_cert(certPem);

  // for some reason, get_oid_value for altNames returns a nested array, e.g.
  // [['host1','host2']], so make it a normal array if necessary
  var altNames = [];
  var origAltNames = x509.get_oid_value(csr, '2.5.29.17');
  if (origAltNames && origAltNames[0] && origAltNames[0][0]) {
    altNames = origAltNames[0];
  }
  return {
    commonName: x509.get_oid_value(csr, '2.5.4.3'),
    altNames
  };
}

/**
 * Convenience method to return the value of a given environment variable or
 * nginx variable. Will return the environment variable if that is found first.
 * Requires that env vars be the uppercase version of nginx vars.
 * If no default is given and the variable is not found, throws an error.
 * @param r Nginx HTTP Request
 * @param varname Name of the variable
 * @returns value of the variable
 */
function getVariable(r, varname, defaultVal) {
  var retval = process.env[varname.toUpperCase()] || r.variables[varname] || defaultVal;
  if (retval === undefined) {
    var errMsg = `Variable ${varname} not found and no default value given.`;
    log$1.error(errMsg);
    throw new Error(errMsg);
  }
  return retval;
}

/**
 * Return the hostname to use as the common name for issued certs. This is the first hostname in the njs_acme_server_names variable.
 * @param r request
 * @returns {string} hostname
 */
function acmeCommonName(r) {
  // The first name is the common name
  return acmeServerNames(r)[0];
}

/**
 * Return the hostname to use as the common name for issued certs. This is the first hostname in the njs_acme_server_names variable.
 * @param r request
 * @returns {string} hostname
 */
function acmeAltNames(r) {
  var serverNames = acmeServerNames(r);
  if (serverNames.length <= 1) {
    // no alt names
    return [];
  }
  // Return everything after the first name
  return serverNames.slice(1);
}

/**
 * Return an array of hostnames specified in the njs_acme_server_names variable
 * @param r request
 * @returns array of hostnames
 */
function acmeServerNames(r) {
  var nameStr = getVariable(r, 'njs_acme_server_names'); // no default == mandatory
  // split string value on comma and/or whitespace and lowercase each element
  var names = nameStr.split(/[,\s]+/);
  var invalidNames = names.filter(name => !isValidHostname(name));
  if (invalidNames.length > 0) {
    var errMsg = 'Invalid hostname(s) in `njs_acme_server_names` detected: ' + invalidNames.join(', ');
    log$1.error(errMsg);
    throw new Error(errMsg);
  }
  return names.map(n => n.toLowerCase());
}

/**
 * Return the path where ACME magic happens
 * @param r request
 * @returns configured path or default
 */
function acmeDir(r) {
  return getVariable(r, 'njs_acme_dir', '/etc/nginx/njs-acme');
}

/**
 * Return the shared_dict zone name
 * @param r request
 * @returns configured shared_dict zone name or default
 */
function acmeZoneName(r) {
  return getVariable(r, 'njs_acme_shared_dict_zone_name', 'acme');
}
/**
 * Return the path where ACME challenges are stored
 * @param r request
 * @returns configured path or default
 */
function acmeChallengeDir(r) {
  return getVariable(r, 'njs_acme_challenge_dir', joinPaths(acmeDir(r), 'challenge'));
}

/**
 * Returns the path for the account private JWK
 * @param r {NginxHTTPRequest}
 */
function acmeAccountPrivateJWKPath(r) {
  return getVariable(r, 'njs_acme_account_private_jwk', joinPaths(acmeDir(r), 'account_private_key.json'));
}

/**
 * Returns the ACME directory URI
 * @param r {NginxHTTPRequest}
 */
function acmeDirectoryURI(r) {
  return getVariable(r, 'njs_acme_directory_uri', 'https://acme-staging-v02.api.letsencrypt.org/directory');
}

/**
 * Returns whether to verify the ACME provider HTTPS certificate and chain
 * @param r {NginxHTTPRequest}
 * @returns boolean
 */
function acmeVerifyProviderHTTPS(r) {
  return ['true', 'yes', '1'].indexOf(getVariable(r, 'njs_acme_verify_provider_https', 'true').toLowerCase().trim()) > -1;
}
function areEqualSets(arr1, arr2) {
  if (arr1.length !== arr2.length) {
    return false;
  }
  for (var _i4 = 0; _i4 < arr1.length; _i4++) {
    var elem = arr1[_i4];
    if (arr2.indexOf(elem) === -1) {
      return false;
    }
  }
  return true;
}

/**
 * Joins args with slashes and removes duplicate slashes
 * @param args path fragments to join
 * @returns joined path string
 */
function joinPaths() {
  for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
    args[_key] = arguments[_key];
  }
  // join args with a slash remove duplicate slashes
  return args.join('/').replace(/\/+/g, '/');
}
function isValidHostname(hostname) {
  return !!hostname && hostname.length < 256 && !!hostname.match(
  // hostnames are dot-separated groups of letters, numbers, hyphens (but
  // not beginning or ending with hyphens), and may end with a period
  /^[a-z\d]([-a-z\d]{0,61}[a-z\d])?(\.[a-z\d]([-a-z\d]{0,61}[a-z\d])?)*\.?$/i);
}

var version = "1.0.0";

/**
 * ACME HTTP client
 *
 * @class HttpClient
 * @param directoryUrl {string} URL to the ACME directory.
 * @param accountKey {CryptoKey} Private key to use for signing requests.
 * @param accountUrl [string] (optional) URL of the account, if it has already been registered.
 * @param externalAccountBinding [ClientExternalAccountBindingOptions] (optional) External account binding options
 * @param verify {boolean} (optional) Enables or disables verification of the HTTPS server certificate while making requests. Defaults to `true`.
 * @param debug {boolean} (optional) Enables debug mode. Defaults to `false`.
 * @param maxBadNonceRetries {number} (optional) Maximum number of retries when encountering a bad nonce error. Defaults to 5.
 */
var HttpClient = /*#__PURE__*/function () {
  /**
   * Creates an instance of the ACME HTTP client.
   * @constructor
   * @param {string} directoryUrl - The URL of the ACME directory.
   * @param {CryptoKey} accountKey - The private key to use for ACME account operations.
   * @param {string} [accountUrl=""] - The URL of the ACME account. If not provided, a new account will be created.
   * @param {ClientExternalAccountBindingOptions} [externalAccountBinding={ kid: "", hmacKey: "" }] - The external account binding options for the client.
   * @returns {HttpClient} The newly created instance of the ACME HTTP client.
   */
  function HttpClient(directoryUrl, accountKey, accountUrl, externalAccountBinding) {
    if (accountUrl === void 0) {
      accountUrl = '';
    }
    if (externalAccountBinding === void 0) {
      externalAccountBinding = {
        kid: '',
        hmacKey: ''
      };
    }
    /**
     * The URL for the ACME directory.
     * @type {string}
     */
    this.directoryUrl = void 0;
    /**
     * The cryptographic key pair used for signing requests.
     * @type {CryptoKey}
     */
    this.accountKey = void 0;
    /**
     * An object that contains external account binding information.
     * @type {ClientExternalAccountBindingOptions}
     */
    this.externalAccountBinding = void 0;
    /**
     * The ACME directory.
     * @type {?AcmeDirectory}
     */
    this.directory = void 0;
    /**
     * The public key in JWK format.
     * @type {?RsaPublicJwk | ?EcdsaPublicJwk}
     */
    this.jwk = void 0;
    /**
     * The URL for the ACME account.
     * @type {?string}
     */
    this.accountUrl = void 0;
    /**
     * Determines whether to verify the HTTPS server certificate while making requests.
     * @type {boolean}
     */
    this.verify = void 0;
    /**
     * The maximum number of retries allowed when encountering a bad nonce.
     * @type {number}
     */
    this.maxBadNonceRetries = void 0;
    this.log = void 0;
    this.directoryUrl = directoryUrl;
    this.accountKey = accountKey;
    this.externalAccountBinding = externalAccountBinding;
    this.directory = null;
    this.jwk = null;
    this.accountUrl = accountUrl;
    this.verify = true;
    this.maxBadNonceRetries = 5;
    this.log = new Logger('http', LogLevel.Info);
  }

  /**
   * HTTP request
   *
   * @param {string} url HTTP URL
   * @param {string} method HTTP method
   * @param {string} [body] Request options
   * @returns {Promise<Response>} HTTP response
   */
  var _proto = HttpClient.prototype;
  _proto.request = function request(url, method, body) {
    try {
      var _this = this;
      if (body === void 0) {
        body = '';
      }
      var options = {
        headers: {
          'user-agent': `njs-acme-v${version}`,
          'Content-Type': 'application/jose+json'
        },
        method: method,
        body: body,
        verify: _this.verify || false
      };

      /* Request */
      _this.log.debug('Sending a new request:', method, url, options);
      return _await(ngx.fetch(url, options), resp => {
        _this.log.debug('Got a response:', resp.status, method, url, resp.headers);
        return resp;
      });
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Sends a signed request to the specified URL with the provided payload.
   * https://tools.ietf.org/html/rfc8555#section-6.2
   *
   * @async
   * @param {string} url - The URL to send the request to.
   * @param {object} payload - The request payload to send.
   * @param {object} options - An object containing optional parameters.
   * @param {string} [options.kid=null] - The kid parameter for the request.
   * @param {string} [options.nonce=null] - The nonce parameter for the request.
   * @param {boolean} [options.includeExternalAccountBinding=false] - Whether to include the externalAccountBinding parameter in the request.
   * @param {number} [attempts=0] - The number of times the request has been attempted.
   * @returns {Promise<Response>} A Promise that resolves with the Response object for the request.
   */
  ;
  _proto.signedRequest = function signedRequest(url, payload, _temp, attempts) {
    try {
      var _this2 = this;
      var _ref = _temp === void 0 ? {} : _temp,
        _ref$kid = _ref.kid,
        kid = _ref$kid === void 0 ? null : _ref$kid,
        _ref$nonce = _ref.nonce,
        nonce = _ref$nonce === void 0 ? null : _ref$nonce,
        _ref$includeExternalA = _ref.includeExternalAccountBinding,
        includeExternalAccountBinding = _ref$includeExternalA === void 0 ? false : _ref$includeExternalA;
      if (attempts === void 0) {
        attempts = 0;
      }
      return _await(_invoke(() => {
        if (!nonce) {
          return _await(_this2.getNonce(), _this2$getNonce => {
            nonce = _this2$getNonce;
          });
        }
      }, () => _invoke(() => {
        if (!_this2.jwk) {
          return _awaitIgnored(_this2.getJwk());
        }
      }, () => {
        _this2.log.debug('Signing request with:', {
          kid,
          nonce,
          jwt: _this2.jwk
        });

        /* External account binding
                 https://datatracker.ietf.org/doc/html/rfc8555#section-7.3.4
                 */
        /* Sign body and send request */
        /* Return response */
        if (includeExternalAccountBinding && _this2.externalAccountBinding) {
          if (_this2.externalAccountBinding.kid && _this2.externalAccountBinding.hmacKey) {
            var jwk = _this2.jwk;
            var eabKid = _this2.externalAccountBinding.kid;
            var eabHmacKey = _this2.externalAccountBinding.hmacKey;

            // FIXME
            if (payload) {
              payload.externalAccountBinding = _this2.createSignedHmacBody(eabHmacKey, url, jwk, {
                kid: eabKid
              });
            }
          }
        }
        return _await(_this2.createSignedBody(url, payload, {
          nonce,
          kid
        }), data => {
          _this2.log.debug('Signed request body:', data);
          return _await(_this2.request(url, 'POST', JSON.stringify(data)), resp => {
            if (resp.status === 400) {
              // Retry on bad nonce - https://tools.ietf.org/html/draft-ietf-acme-acme-10#section-6.4
              // or bad response code.
              if (attempts < _this2.maxBadNonceRetries) {
                nonce = resp.headers.get('replay-nonce') || null;
                attempts += 1;
                _this2.log.warn(`Error response from server, retrying (${attempts}/${_this2.maxBadNonceRetries}) signed request to: ${url}`);
                return _this2.signedRequest(url, payload, {
                  kid,
                  nonce,
                  includeExternalAccountBinding
                }, attempts);
              }
            }
            return resp;
          });
        });
      })));
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Sends a signed ACME API request with optional JWS authentication, nonce handling, and external account binding
   * request to the specified URL with the provided payload, and verifies the response status code.
   *
   * @param {string} url - The URL to make the API request to.
   * @param {any} [payload=null] - The payload to include in the API request.
   * @param {number[]} [validStatusCodes=[]] - An array of valid HTTP status codes.
   * @param {Object} [options={}] - An object of options for the API request.
   * @param {boolean} [options.includeJwsKid=true] - Whether to include the JWS kid header in the API request.
   * @param {boolean} [options.includeExternalAccountBinding=false] - Whether to include the external account binding in the API request.
   * @returns {Promise<Response>} - A promise that resolves with the API response.
   * @throws {Error} When an unexpected status code is returned in the HTTP response, with the corresponding error message returned in the response body.
   */
  ;
  _proto.apiRequest = function apiRequest(url, payload, validStatusCodes, _temp2) {
    try {
      var _this3 = this;
      if (payload === void 0) {
        payload = null;
      }
      if (validStatusCodes === void 0) {
        validStatusCodes = [];
      }
      var _ref2 = _temp2 === void 0 ? {} : _temp2,
        _ref2$includeJwsKid = _ref2.includeJwsKid,
        includeJwsKid = _ref2$includeJwsKid === void 0 ? true : _ref2$includeJwsKid,
        _ref2$includeExternal = _ref2.includeExternalAccountBinding,
        includeExternalAccountBinding = _ref2$includeExternal === void 0 ? false : _ref2$includeExternal;
      var kid = includeJwsKid ? _this3.getAccountUrl() : null;
      _this3.log.debug('Preparing a new api request:', {
        kid,
        payload
      });
      return _await(_this3.signedRequest(url, payload, {
        kid,
        includeExternalAccountBinding
      }), resp => {
        var _exit = false;
        return _invoke(() => {
          if (validStatusCodes.length && validStatusCodes.indexOf(resp.status) === -1) {
            return _await(resp.json(), b => {
              _this3.log.warn(`Received unexpected status code ${resp.status} for API request ${url}.`, 'Expected status codes:', validStatusCodes, 'Body response:', b);
              var e = formatResponseError(b);
              throw new Error(e);
            });
          }
        }, _result => _exit ? _result : resp);
      });
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * ACME API request by resource name helper
   *
   * @private
   * @param {string} resource Request resource name
   * @param {object} [payload] Request payload, default: `null`
   * @param {array} [validStatusCodes] Array of valid HTTP response status codes, default: `[]`
   * @param {object} [opts]
   * @param {boolean} [opts.includeJwsKid] Include KID instead of JWK in JWS header, default: `true`
   * @param {boolean} [opts.includeExternalAccountBinding] Include EAB in request, default: `false`
   * @returns {Promise<object>} HTTP response
   */
  ;
  _proto.apiResourceRequest = function apiResourceRequest(resource, payload, validStatusCodes, _temp3) {
    try {
      var _this4 = this;
      if (validStatusCodes === void 0) {
        validStatusCodes = [];
      }
      var _ref3 = _temp3 === void 0 ? {} : _temp3,
        _ref3$includeJwsKid = _ref3.includeJwsKid,
        includeJwsKid = _ref3$includeJwsKid === void 0 ? true : _ref3$includeJwsKid,
        _ref3$includeExternal = _ref3.includeExternalAccountBinding,
        includeExternalAccountBinding = _ref3$includeExternal === void 0 ? false : _ref3$includeExternal;
      return _await(_this4.getResourceUrl(resource), resourceUrl => _this4.apiRequest(resourceUrl, payload, validStatusCodes, {
        includeJwsKid,
        includeExternalAccountBinding
      }));
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Retrieves the ACME directory from the directory URL specified in the constructor.
   *
   * @throws {Error} Throws an error if the response status code is not 200 OK or the response body is invalid.
   * @returns {Promise<void>} Updates internal `this.directory` and returns a promise
   */
  ;
  _proto.getDirectory = function getDirectory() {
    try {
      var _this5 = this;
      return _await((() => {
        if (!_this5.directory) {
          return _await(_this5.request(_this5.directoryUrl, 'GET'), resp => {
            if (resp.status >= 400) {
              throw new Error(`Attempting to read ACME directory returned error ${resp.status}: ${_this5.directoryUrl}`);
            }
            return _await(resp.json(), _resp$json => {
              var data = _resp$json;
              if (!data) {
                throw new Error('Attempting to read ACME directory returned no data');
              }
              _this5.directory = data;
              _this5.log.debug('Fetched directory:', _this5.directory);
            });
          });
        }
      })());
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Retrieves the public key associated with the account key
   *
   * @async
   * @function getJwk
   * @returns {Promise<RsaPublicJwk|EcdsaPublicJwk|null>} The public key associated with the account key, or null if not found
   * @throws {Error} If the account key is not set or is not valid
   */
  ;
  _proto.getJwk = function getJwk() {
    try {
      var _this6 = this;
      // singleton
      return _await(_invoke(() => {
        if (!_this6.jwk) {
          _this6.log.debug('Public JWK not set. Obtaining it from Account Private Key...');
          return _await(getPublicJwk(_this6.accountKey), _getPublicJwk => {
            _this6.jwk = _getPublicJwk;
            _this6.log.debug('Obtained Account Public JWK:', _this6.jwk);
          });
        }
      }, () => _this6.jwk));
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Get nonce from directory API endpoint
   *
   * https://tools.ietf.org/html/rfc8555#section-7.2
   *
   * @returns {Promise<string>} nonce
   */
  ;
  _proto.getNonce = function getNonce() {
    try {
      var _this7 = this;
      return _await(_this7.getResourceUrl('newNonce'), url => _await(_this7.request(url, 'HEAD'), resp => {
        if (!resp.headers.get('replay-nonce')) {
          _this7.log.error('No nonce from ACME provider. "replay-nonce" header found');
          throw new Error('Failed to get nonce from ACME provider');
        }
        return resp.headers.get('replay-nonce');
      }));
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Get URL for a directory resource
   *
   * @param {string} resource API resource name
   * @returns {Promise<string>} URL
   */
  ;
  _proto.getResourceUrl = function getResourceUrl(resource) {
    try {
      var _this8 = this;
      return _await(_this8.getDirectory(), () => {
        if (_this8.directory != null && !_this8.directory[resource]) {
          _this8.log.error(`Unable to locate API resource URL in ACME directory: "${resource}"`);
          throw new Error(`Unable to locate API resource URL in ACME directory: "${resource}"`);
        }
        if (!_this8.directory) {
          throw new Error('this.directory is null');
        }
        return _this8.directory[resource];
      });
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Get directory meta field
   *
   * @param {string} field Meta field name
   * @returns {Promise<string | boolean | string[] | undefined>} Meta field value
   */
  ;
  _proto.getMetaField = function getMetaField(field) {
    try {
      var _this9 = this;
      return _await(_this9.getDirectory(), () => {
        var _this9$directory, _this9$directory$meta;
        if (!_this9.directory) {
          throw new Error('this.directory is null');
        }
        return (_this9$directory = _this9.directory) == null ? void 0 : (_this9$directory$meta = _this9$directory.meta) == null ? void 0 : _this9$directory$meta[field];
      });
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Prepares a signed request body to be sent to an ACME server.
   * @param {AcmeSignAlgo|string} alg - The signing algorithm to use.
   * @param {NjsStringLike} url - The URL to include in the signed payload.
   * @param {Object|null} [payload=null] - The payload to include in the signed payload.
   * @param {RsaPublicJwk|EcdsaPublicJwk|null|undefined} [jwk=null] - The JWK to use for signing the payload.
   * @param {Object} [options={nonce: null, kid: null}] - Additional options for the signed payload.
   * @param {string|null} [options.nonce=null] - The nonce to include in the signed payload.
   * @param {string|null} [options.kid=null] - The KID to include in the signed payload.
   * @returns {SignedPayload} The signed payload.
   */
  ;
  _proto.prepareSignedBody = function prepareSignedBody(alg, url, payload, jwk, _temp4) {
    if (payload === void 0) {
      payload = null;
    }
    var _ref4 = _temp4 === void 0 ? {} : _temp4,
      _ref4$nonce = _ref4.nonce,
      nonce = _ref4$nonce === void 0 ? null : _ref4$nonce,
      _ref4$kid = _ref4.kid,
      kid = _ref4$kid === void 0 ? null : _ref4$kid;
    var header = {
      alg,
      url
    };

    /* Nonce */
    if (nonce) {
      header.nonce = nonce;
    }

    /* KID or JWK */
    if (kid) {
      header.kid = kid;
    } else {
      header.jwk = jwk;
    }

    /* Body */
    var body = {
      payload: payload ? Buffer.from(JSON.stringify(payload)).toString('base64url') : '',
      protected: Buffer.from(JSON.stringify(header)).toString('base64url')
    };
    return body;
  }

  /**
   * Creates a signed HMAC body for the given URL and payload, with optional nonce and kid parameters
   *
   * @param {string} hmacKey The key to use for the HMAC signature.
   * @param {string} url The URL to sign.
   * @param {object} [payload] The payload to sign. Defaults to null.
   * @param {object} [opts] Optional parameters for the signature (nonce and kid).
   * @param {string} [opts.nonce] The anti-replay nonce to include in the signature. Defaults to null.
   * @param {string} [opts.kid] The kid to include in the signature. Defaults to null.
   * @returns {object} Signed HMAC request body
   * @throws An error if the HMAC key is not provided.
   */;
  _proto.createSignedHmacBody = function createSignedHmacBody(hmacKey, url, payload, _temp5) {
    try {
      var _this10 = this;
      if (payload === void 0) {
        payload = null;
      }
      var _ref5 = _temp5 === void 0 ? {} : _temp5,
        _ref5$nonce = _ref5.nonce,
        nonce = _ref5$nonce === void 0 ? null : _ref5$nonce,
        _ref5$kid = _ref5.kid,
        kid = _ref5$kid === void 0 ? null : _ref5$kid;
      if (!hmacKey) {
        throw new Error('HMAC key is required.');
      }
      var result = _this10.prepareSignedBody('HS256', url, payload, null, {
        nonce,
        kid
      });
      var h = OGCrypto.createHmac('sha256', Buffer.from(hmacKey, 'base64'));
      h.update(`${result.protected}.${result.payload}`);
      result.signature = h.digest('base64url');
      return _await(result);
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Create JWS HTTP request body using RSA or ECC
   *
   * https://datatracker.ietf.org/doc/html/rfc7515
   *
   * @param {string} url Request URL
   * @param {object} [payload] Request payload
   * @param {object} [opts]
   * @param {string} [opts.nonce] JWS nonce
   * @param {string} [opts.kid] JWS KID
   * @returns {Promise<SignedPayload>} JWS request body
   */
  ;
  _proto.createSignedBody = function createSignedBody(url, payload, _temp6) {
    try {
      var _this11 = this;
      if (payload === void 0) {
        payload = null;
      }
      var _ref6 = _temp6 === void 0 ? {} : _temp6,
        _ref6$nonce = _ref6.nonce,
        nonce = _ref6$nonce === void 0 ? null : _ref6$nonce,
        _ref6$kid = _ref6.kid,
        kid = _ref6$kid === void 0 ? null : _ref6$kid;
      var jwk = _this11.jwk;
      var headerAlg = 'RS256';
      var signerAlg = 'SHA-256';
      if (!jwk) {
        throw new Error('jwk is undefined');
      }
      /* https://datatracker.ietf.org/doc/html/rfc7518#section-3.1 */
      if ('crv' in jwk && jwk.crv && jwk.kty === 'EC') {
        headerAlg = 'ES256';
        if (jwk.crv === 'P-384') {
          headerAlg = 'ES384';
          signerAlg = 'SHA-384';
        } else if (jwk.crv === 'P-521') {
          headerAlg = 'ES512';
          signerAlg = 'SHA-512';
        }
      }

      /* Prepare body and sign it */
      var result = _this11.prepareSignedBody(headerAlg, url, payload, jwk, {
        nonce,
        kid
      });
      _this11.log.debug('Prepared signed payload', result);
      var sign;
      return _await(_invoke(() => {
        if (jwk.kty === 'EC') {
          return _await(crypto.subtle.digest(signerAlg, `${result.protected}.${result.payload}`), hash => _await(crypto.subtle.sign({
            name: 'ECDSA',
            hash: hash.toString()
          }, _this11.accountKey, hash), _crypto$subtle$sign => {
            sign = _crypto$subtle$sign;
          }));
        } else {
          return _await(crypto.subtle.sign({
            name: 'RSASSA-PKCS1-v1_5'
          }, _this11.accountKey, `${result.protected}.${result.payload}`), _crypto$subtle$sign2 => {
            sign = _crypto$subtle$sign2;
          });
        }
      }, () => {
        result.signature = Buffer.from(sign).toString('base64url');
        return result;
      }));
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Returns the account URL associated with the current client instance.
   *
   * @private
   * @returns {string} the account URL
   * @throws {Error} If no account URL has been set yet
   */
  ;
  _proto.getAccountUrl = function getAccountUrl() {
    if (!this.accountUrl) {
      throw new Error('No account URL found, register account first');
    }
    return this.accountUrl;
  }

  /**
   * Get Terms of Service URL if available
   *
   * https://tools.ietf.org/html/rfc8555#section-7.1.1
   *
   * @returns {Promise<string|null>} ToS URL
   */;
  _proto.getTermsOfServiceUrl = function getTermsOfServiceUrl() {
    try {
      var _this12 = this;
      return _await(_this12.getMetaField('termsOfService'));
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Create new account
   *
   * https://tools.ietf.org/html/rfc8555#section-7.3
   *
   * @param {object} data Request payload.
   * @param {boolean} data.termsOfServiceAgreed Whether the client agrees to the terms of service.
   * @param {[]string} data.contact An array of contact info, e.g. ['mailto:admin@example.com'].
   * @param {boolean} data.onlyReturnExisting Whether the server should only return an existing account, or create a new one if it does not exist.
   * @returns {Promise<object>} HTTP response.
   */
  ;
  _proto.createAccount = function createAccount(data) {
    try {
      var _this13 = this;
      return _await(_this13.apiResourceRequest('newAccount', data, [200, 201], {
        includeJwsKid: false,
        includeExternalAccountBinding: data.onlyReturnExisting !== true
      }), resp => {
        /* Set account URL */
        if (resp.headers.get('location')) {
          _this13.accountUrl = resp.headers.get('location');
        }
        return resp;
      });
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Update account
   *
   * https://tools.ietf.org/html/rfc8555#section-7.3.2
   *
   * @param {object} data Request payload
   * @returns {Promise<object>} HTTP response
   */
  ;
  _proto.updateAccount = function updateAccount(data) {
    return this.apiRequest(this.getAccountUrl(), data, [200, 202]);
  }

  /**
   * Update account key
   *
   * https://tools.ietf.org/html/rfc8555#section-7.3.5
   *
   * @param {ApiPayload} data Request payload
   * @returns {Promise<object>} HTTP response
   */;
  _proto.updateAccountKey = function updateAccountKey(data) {
    return this.apiResourceRequest('keyChange', data, [200]);
  }

  /**
   * Create new order
   *
   * https://tools.ietf.org/html/rfc8555#section-7.4
   *
   * @param {ApiPayload} data Request payload
   * @returns {Promise<object>} HTTP response
   */;
  _proto.createOrder = function createOrder(data) {
    return this.apiResourceRequest('newOrder', data, [201]);
  }

  /**
   * Get order
   *
   * https://tools.ietf.org/html/rfc8555#section-7.4
   *
   * @param {string} url Order URL
   * @returns {Promise<object>} HTTP response
   */;
  _proto.getOrder = function getOrder(url) {
    return this.apiRequest(url, null, [200]);
  }

  /**
   * Finalize order
   *
   * https://tools.ietf.org/html/rfc8555#section-7.4
   *
   * @param {string} url Finalization URL
   * @param {ApiPayload} data Request payload
   * @returns {Promise<object>} HTTP response
   */;
  _proto.finalizeOrder = function finalizeOrder(url, data) {
    return this.apiRequest(url, data, [200]);
  }

  /**
   * Get identifier authorization
   *
   * https://tools.ietf.org/html/rfc8555#section-7.5
   *
   * @param {string} url Authorization URL
   * @returns {Promise<object>} HTTP response
   */;
  _proto.getAuthorization = function getAuthorization(url) {
    return this.apiRequest(url, null, [200]);
  }

  /**
   * Update identifier authorization
   *
   * https://tools.ietf.org/html/rfc8555#section-7.5.2
   *
   * @param {string} url Authorization URL
   * @param {object} data Request payload
   * @returns {Promise<object>} HTTP response
   */;
  _proto.updateAuthorization = function updateAuthorization(url, data) {
    return this.apiRequest(url, data, [200]);
  }

  /**
   * Completes a pending challenge with the ACME server by sending a response payload to the challenge URL.
   *
   * https://tools.ietf.org/html/rfc8555#section-7.5.1
   *
   * @param {string} url Challenge URL
   * @param {ApiPayload} data Request payload
   * @returns {Promise<object>} HTTP response
   */;
  _proto.completeChallenge = function completeChallenge(url, data) {
    return this.apiRequest(url, data, [200]);
  }

  /**
   * Revoke certificate
   *
   * https://tools.ietf.org/html/rfc8555#section-7.6
   *
   *
   * @param {ApiPayload} data - An object containing the data needed for revocation:
   * @param {string} data.certificate - The certificate to be revoked.
   * @param {number} data.reason - An optional reason for revocation (default: 1).
   *                               See this https://datatracker.ietf.org/doc/html/rfc5280#section-5.3.1
   * @returns {Promise<object>} HTTP response
   */;
  _proto.revokeCert = function revokeCert(data) {
    return this.apiResourceRequest('revokeCert', data, [200]);
  }

  /**
   * Set the `verify` property to enable or disable verification of the HTTPS server certificate.
   *
   * @param {boolean} v - The value to set `verify` to.
   */;
  _proto.setVerify = function setVerify(v) {
    this.verify = v;
  }

  /** how verbose these logs will be */;
  _createClass(HttpClient, [{
    key: "minLevel",
    get: function () {
      return this.log.minLevel;
    }
    /** controls how verbose these logs will be */,
    set: function (v) {
      this.log.minLevel = v;
    }
  }]);
  return HttpClient;
}();

/* rfc 8555 */
/**
 * Account
 *
 * https://tools.ietf.org/html/rfc8555#section-7.1.2
 * https://tools.ietf.org/html/rfc8555#section-7.3
 * https://tools.ietf.org/html/rfc8555#section-7.3.2
 */
/**
 * Order
 *
 * https://tools.ietf.org/html/rfc8555#section-7.1.3
 * https://tools.ietf.org/html/rfc8555#section-7.4
 */
/**
 * Authorization
 *
 * https://tools.ietf.org/html/rfc8555#section-7.1.4
 */
/**
 * Challenge
 *
 * https://tools.ietf.org/html/rfc8555#section-8
 * https://tools.ietf.org/html/rfc8555#section-8.3
 * https://tools.ietf.org/html/rfc8555#section-8.4
 */
/**
 * ACME client auto mode
 *
 * @param {AcmeClient} client ACME client
 * @param {ClientAutoOptions} userOpts Options
 * @returns {Promise<string>} Certificate
 */
var _auto = _async((client, userOpts) => {
  var opts = Object.assign({}, autoDefaultOpts, userOpts);
  var log = new Logger('auto', client.minLevel);
  var accountPayload = {
    termsOfServiceAgreed: opts.termsOfServiceAgreed
  };
  if (!Buffer.isBuffer(opts.csr) && opts.csr) {
    opts.csr = Buffer.from(opts.csr);
  }
  if (opts.email) {
    accountPayload.contact = [`mailto:${opts.email}`];
  }

  /**
   * Register account
   */
  log.info('Checking account');
  return _continue(_catch(() => {
    client.getAccountUrl();
    log.info('Account URL already exists, skipping account registration');
  }, () => {
    log.info('Registering account');
    return _awaitIgnored(client.createAccount(accountPayload));
  }), () => {
    /**
     * Parse domains from CSR
     */
    log.info('Parsing domains from Certificate Signing Request');
    if (opts.csr === null) {
      throw new Error('csr is required');
    }
    var csrDomains = readX509ServerNames(toPEM(opts.csr, 'CERTIFICATE REQUEST'));
    var domains = uniqueDomains(csrDomains);
    log.info(`Resolved ${domains.length} unique domains (${domains.join(', ')}) from parsing the Certificate Signing Request`);

    /**
     * Place order
     */
    var orderPayload = {
      identifiers: domains.map(d => ({
        type: 'dns',
        value: d
      }))
    };
    return _await(client.createOrder(orderPayload), order => _await(client.getAuthorizations(order), authorizations => {
      log.info(`Placed certificate order successfully`);

      /**
       * Resolve and satisfy challenges
       */
      log.info('Resolving and satisfying authorization challenges');
      var challengePromises = authorizations.map(_async(authz => {
        var _authz$identifier;
        var d = (_authz$identifier = authz.identifier) == null ? void 0 : _authz$identifier.value;
        var challengeCompleted = false;

        /* Skip authz that already has valid status */
        if (authz.status === 'valid') {
          log.info(`[${d}] Authorization already has valid status, no need to complete challenges`);
          return;
        }
        return _catch(() => {
          var _authz$challenges;
          /* Select challenge based on priority */
          var challenge = (_authz$challenges = authz.challenges) == null ? void 0 : _authz$challenges.sort((a, b) => {
            var aidx = opts.challengePriority.indexOf(a.type);
            var bidx = opts.challengePriority.indexOf(b.type);
            if (aidx === -1) return 1;
            if (bidx === -1) return -1;
            return aidx - bidx;
          }).slice(0, 1)[0];
          if (!challenge) {
            throw new Error(`Unable to select challenge for ${d}, no challenge found`);
          }
          log.info(`[${d}] Found ${authz.challenges.length} challenges, selected type: ${challenge.type}`);

          /* Trigger challengeCreateFn() */
          return _await(client.getChallengeKeyAuthorization(challenge), keyAuthorization => _continueIgnored(_finallyRethrows(() => _await(opts.challengeCreateFn(authz, challenge, keyAuthorization), () => {
            /* Complete challenge and wait for valid status */
            log.info(`[${d}] Completing challenge with ACME provider and waiting for valid status`);
            return _await(client.completeChallenge(challenge), () => {
              challengeCompleted = true;
              return _awaitIgnored(client.waitForValidStatus(challenge));
            });
          }), (_wasThrown, _result4) => {
            /* Trigger challengeRemoveFn(), suppress errors */
            return _continue(_catch(() => _awaitIgnored(opts.challengeRemoveFn(authz, challenge, keyAuthorization)), e => {
              log.info(`[${d}] challengeRemoveFn threw error: ${e.message}`);
            }), () => _rethrow(_wasThrown, _result4));
          })));
        }, e => {
          /* Deactivate pending authz when unable to complete challenge */
          return _invoke(() => {
            if (!challengeCompleted) {
              log.info(`[${d}] Unable to complete challenge: ${e.message}`);
              return _continueIgnored(_catch(() => _awaitIgnored(client.deactivateAuthorization(authz)), f => {
                /* Suppress deactivateAuthorization() errors */
                log.info(`[${d}] Authorization deactivation threw error: ${f.message}`);
              }));
            }
          }, () => {
            throw e;
          });
        });
      }));
      log.info('Waiting for challenge valid status');
      return _await(Promise.all(challengePromises), () => {
        if (!opts.csr) {
          throw new Error('options is missing required csr');
        }

        /**
         * Finalize order and download certificate
         */
        log.info('Finalize order and download certificate');
        return _await(client.finalizeOrder(order, opts.csr), finalized => _await(client.getCertificate(finalized, opts.preferredChain)));
      });
    }));
  });
});
var autoDefaultOpts = {
  challengePriority: ['http-01'],
  termsOfServiceAgreed: false,
  challengeCreateFn: _async((_authz, _challenge, _keyAuthorization) => {
    throw new Error('Missing challengeCreateFn()');
  }),
  challengeRemoveFn: _async((_authz, _challenge, _keyAuthorization) => {
    throw new Error('Missing challengeRemoveFn()');
  })
};
/**
 * ACME states
 *
 * @private
 */

var validStates = ['ready', 'valid'];
var pendingStates = ['pending', 'processing'];
var invalidStates = ['invalid'];

/**
 * Default options
 *
 * @private
 */
var defaultOpts = {
  directoryUrl: undefined,
  accountKey: undefined,
  accountUrl: null,
  externalAccountBinding: {},
  backoffAttempts: 10,
  backoffMin: 3000,
  backoffMax: 30000
};

/**
 * AcmeClient
 *
 * @class
 * @param {object} opts
 * @param {string} opts.directoryUrl ACME directory URL
 * @param {buffer|string} opts.accountKey PEM encoded account private key
 * @param {string} [opts.accountUrl] Account URL, default: `null`
 * @param {object} [opts.externalAccountBinding]
 * @param {string} [opts.externalAccountBinding.kid] External account binding KID
 * @param {string} [opts.externalAccountBinding.hmacKey] External account binding HMAC key
 * @param {number} [opts.backoffAttempts] Maximum number of backoff attempts, default: `10`
 * @param {number} [opts.backoffMin] Minimum backoff attempt delay in milliseconds, default: `5000`
 * @param {number} [opts.backoffMax] Maximum backoff attempt delay in milliseconds, default: `30000`
 *
 * @example Create ACME client instance
 * ```js
 * const client = new acme.Client({
 *     directoryUrl: acme.directory.letsencrypt.staging,
 *     accountKey: 'Private key goes here'
 * });
 * ```
 *
 * @example Create ACME client instance
 * ```js
 * const client = new acme.Client({
 *     directoryUrl: acme.directory.letsencrypt.staging,
 *     accountKey: <'Private key goes here'>,
 *     accountUrl: 'Optional account URL goes here',
 *     backoffAttempts: 10,
 *     backoffMin: 5000,
 *     backoffMax: 30000
 * });
 * ```
 *
 * @example Create ACME client with external account binding
 * ```js
 * const client = new acme.Client({
 *     directoryUrl: 'https://acme-provider.example.com/directory-url',
 *     accountKey: 'Private key goes here',
 *     externalAccountBinding: {
 *         kid: 'YOUR-EAB-KID',
 *         hmacKey: 'YOUR-EAB-HMAC-KEY'
 *     }
 * });
 * ```
 */
var AcmeClient = /*#__PURE__*/function () {
  function AcmeClient(opts) {
    this.opts = void 0;
    this.backoffOpts = void 0;
    this.api = void 0;
    this.log = void 0;
    // if (!Buffer.isBuffer(opts.accountKey)) {
    //     opts.accountKey = Buffer.from(opts.accountKey);
    // }

    this.opts = Object.assign({}, defaultOpts, opts);
    this.backoffOpts = {
      attempts: this.opts.backoffAttempts,
      min: this.opts.backoffMin,
      max: this.opts.backoffMax
    };
    this.log = new Logger('client', LogLevel.Info);

    // FIXME accountKey - is a CryptoKey object not a PEM/string/Object...
    this.api = new HttpClient(this.opts.directoryUrl, this.opts.accountKey, this.opts.accountUrl);
  }

  /**
   * Get Terms of Service URL if available
   *
   * @returns {Promise<string|null>} ToS URL
   *
   * @example Get Terms of Service URL
   * ```js
   * const termsOfService = client.getTermsOfServiceUrl();
   *
   * if (!termsOfService) {
   *     // CA did not provide Terms of Service
   * }
   * ```
   */
  var _proto = AcmeClient.prototype;
  _proto.getTermsOfServiceUrl = function getTermsOfServiceUrl() {
    try {
      var _this = this;
      return _await(_this.api.getTermsOfServiceUrl());
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Get current account URL
   *
   * @returns {string} Account URL
   * @throws {Error} No account URL found
   *
   * @example Get current account URL
   * ```js
   * try {
   *     const accountUrl = client.getAccountUrl();
   * }
   * catch (e) {
   *     // No account URL exists, need to create account first
   * }
   * ```
   */
  ;
  _proto.getAccountUrl = function getAccountUrl() {
    return this.api.getAccountUrl();
  }

  /**
   * Create a new account
   *
   * https://tools.ietf.org/html/rfc8555#section-7.3
   *
   * @param {object} [data] Request data
   * @returns {Promise<object>} Account
   *
   * @example Create a new account
   * ```js
   * const account = await client.createAccount({
   *     termsOfServiceAgreed: true
   * });
   * ```
   *
   * @example Create a new account with contact info
   * ```js
   * const account = await client.createAccount({
   *     termsOfServiceAgreed: true,
   *     contact: ['mailto:test@example.com']
   * });
   * ```
   */;
  _proto.createAccount = function createAccount(data) {
    try {
      var _this2 = this;
      if (data === void 0) {
        data = {
          termsOfServiceAgreed: false
        };
      }
      return _await(_catch(() => {
        _this2.getAccountUrl();

        /* Account URL exists */
        _this2.log.info('Account URL exists, updating it...');
        return _await(_this2.updateAccount(data));
      }, () => {
        return _await(_this2.api.createAccount(data), resp => {
          var _exit = false;
          /* HTTP 200: Account exists */
          return _invoke(() => {
            if (resp.status === 200) {
              _this2.log.info('Account already exists (HTTP 200), updating it...');
              return _await(_this2.updateAccount(data), _await$_this2$updateA => {
                _exit = true;
                return _await$_this2$updateA;
              });
            }
          }, _result => _exit ? _result : _await(resp.json(), _resp$json => _resp$json));
        });
      }));
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Update existing account
   *
   * https://tools.ietf.org/html/rfc8555#section-7.3.2
   *
   * @param {object} [data] Request data
   * @returns {Promise<object>} Account
   *
   * @example Update existing account
   * ```js
   * const account = await client.updateAccount({
   *     contact: ['mailto:foo@example.com']
   * });
   * ```
   */
  ;
  _proto.updateAccount = function updateAccount(data) {
    try {
      var _this3 = this;
      if (data === void 0) {
        data = {};
      }
      try {
        _this3.api.getAccountUrl();
      } catch (e) {
        return _await(_this3.createAccount(data || undefined));
      }

      /* Remove data only applicable to createAccount() */
      if (data && 'onlyReturnExisting' in data) {
        delete data.onlyReturnExisting;
      }

      /* POST-as-GET */
      if (data && Object.keys(data).length === 0) {
        data = null;
      }
      return _await(_this3.api.updateAccount(data), resp => _await(resp.json(), _resp$json2 => _resp$json2));
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Update account private key
   *
   * https://tools.ietf.org/html/rfc8555#section-7.3.5
   *
   * @param {CryptoKey} newAccountKey New account private key
   * @param {object} [data] Additional request data
   * @returns {Promise<object>} Account
   *
   * @example Update account private key
   * ```js
   * const newAccountKey = 'New private key goes here';
   * const result = await client.updateAccountKey(newAccountKey);
   * ```
   */
  ;
  _proto.updateAccountKey = function updateAccountKey(newAccountKey, data) {
    try {
      var _this4 = this;
      if (data === void 0) {
        data = {};
      }
      var accountUrl = _this4.api.getAccountUrl();

      /* Create new HTTP and API clients using new key */
      var newHttpClient = new HttpClient(_this4.opts.directoryUrl, newAccountKey, accountUrl);

      /* Get old JWK */
      data.account = accountUrl;
      data.oldKey = _this4.api.getJwk();

      /* Get signed request body from new client */
      return _await(newHttpClient.getResourceUrl('keyChange'), url => _await(newHttpClient.createSignedBody(url, data), body => _await(_this4.api.updateAccountKey(body), resp => {
        /* Replace existing HTTP and API client */
        _this4.api = newHttpClient;

        // FIXME
        return _await(resp.json(), _resp$json3 => _resp$json3);
      })));
      /* Change key using old client */
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Create a new order
   *
   * https://tools.ietf.org/html/rfc8555#section-7.4
   *
   * @param {object} data Request data
   * @returns {Promise<object>} Order
   *
   * @example Create a new order
   * ```js
   * const order = await client.createOrder({
   *     identifiers: [
   *         { type: 'dns', value: 'example.com' },
   *         { type: 'dns', value: 'test.example.com' }
   *     ]
   * });
   * ```
   */
  ;
  _proto.createOrder = function createOrder(data) {
    try {
      var _this5 = this;
      return _await(_this5.api.createOrder(data), resp => {
        if (!resp.headers.get('location')) {
          throw new Error('Creating a new order did not return an order link');
        }

        // FIXME
        /* Add URL to response */
        return _await(resp.json(), _resp$json4 => {
          var respData = _resp$json4;
          respData.url = resp.headers.get('location');
          return respData;
        });
      });
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Refresh order object from CA
   *
   * https://tools.ietf.org/html/rfc8555#section-7.4
   *
   * @param {object} order Order object
   * @returns {Promise<object>} Order
   *
   * @example
   * ```js
   * const order = { ... }; // Previously created order object
   * const result = await client.getOrder(order);
   * ```
   */
  ;
  _proto.getOrder = function getOrder(order) {
    try {
      var _this6 = this;
      if (!order.url) {
        throw new Error('Unable to get order, URL not found');
      }
      return _await(_this6.api.getOrder(order.url), resp => _await(resp.json(), _resp$json5 => {
        var respData = _resp$json5;
        respData.url = order.url;
        return respData;
      }));
      /* Add URL to response */
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Finalize order
   *
   * https://tools.ietf.org/html/rfc8555#section-7.4
   *
   * @param {object} order Order object
   * @param {buffer|string} csr PEM encoded Certificate Signing Request
   * @returns {Promise<object>} Order
   *
   * @example Finalize order
   * ```js
   * const order = { ... }; // Previously created order object
   * const csr = { ... }; // Previously created Certificate Signing Request
   * const result = await client.finalizeOrder(order, csr);
   * ```
   */
  ;
  _proto.finalizeOrder = function finalizeOrder(order, csr) {
    try {
      var _exit2 = false;
      var _this7 = this;
      if (!order.finalize) {
        throw new Error('Unable to finalize order, URL not found');
      }
      if (!Buffer.isBuffer(csr)) {
        csr = Buffer.from(csr);
      }
      var data = {
        csr: getPemBodyAsB64u(csr)
      };
      var resp;
      return _await(_continue(_catch(() => _await(_this7.api.finalizeOrder(order.finalize, data), _this7$api$finalizeOr => {
        resp = _this7$api$finalizeOr;
      }), e => {
        _this7.log.warn('finalize order failed:', e);
        throw e;
      }), _result2 => _exit2 ? _result2 : _await(resp.json(), _resp$json6 => {
        var respData = _resp$json6;
        respData.url = order.url;
        return respData;
      })));
      /* Add URL to response */
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Get identifier authorizations from order
   *
   * https://tools.ietf.org/html/rfc8555#section-7.5
   *
   * @param {object} order Order
   * @returns {Promise<object[]>} Authorizations
   *
   * @example Get identifier authorizations
   * ```js
   * const order = { ... }; // Previously created order object
   * const authorizations = await client.getAuthorizations(order);
   *
   * authorizations.forEach((authz) => {
   *     const { challenges } = authz;
   * });
   * ```
   */
  ;
  _proto.getAuthorizations = function getAuthorizations(order) {
    try {
      var _this8 = this;
      return Promise.all((order.authorizations || []).map(_async(url => _await(_this8.api.getAuthorization(url), resp => _await(resp.json(), _resp$json7 => {
        var respData = _resp$json7;
        /* Add URL to response */
        respData.url = url;
        return respData;
      })))));
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Deactivate identifier authorization
   *
   * https://tools.ietf.org/html/rfc8555#section-7.5.2
   *
   * @param {object} authz Identifier authorization
   * @returns {Promise<object>} Authorization
   *
   * @example Deactivate identifier authorization
   * ```js
   * const authz = { ... }; // Identifier authorization resolved from previously created order
   * const result = await client.deactivateAuthorization(authz);
   * ```
   */
  ;
  _proto.deactivateAuthorization = function deactivateAuthorization(authz) {
    try {
      var _this9 = this;
      if (!authz.url) {
        throw new Error('Unable to deactivate identifier authorization, URL not found');
      }
      var data = {
        status: 'deactivated'
      };
      return _await(_this9.api.updateAuthorization(authz.url, data), resp => _await(resp.json(), _resp$json8 => {
        var respData = _resp$json8;
        respData.url = authz.url;
        return respData;
      }));
      /* Add URL to response */
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Get key authorization for ACME challenge
   *
   * https://tools.ietf.org/html/rfc8555#section-8.1
   *
   * @param {object} challenge Challenge object returned by API
   * @returns {Promise<string>} Key authorization
   *
   * @example Get challenge key authorization
   * ```js
   * const challenge = { ... }; // Challenge from previously resolved identifier authorization
   * const key = await client.getChallengeKeyAuthorization(challenge);
   *
   * // Write key somewhere to satisfy challenge
   * ```
   */
  ;
  _proto.getChallengeKeyAuthorization = function getChallengeKeyAuthorization(challenge) {
    try {
      var _this10 = this;
      return _await(_this10.api.getJwk(), jwk => {
        var keysum = OGCrypto.createHash('sha256').update(JSON.stringify(jwk));
        var thumbprint = keysum.digest('base64url');
        var result = `${challenge.token}.${thumbprint}`;

        /**
         * https://tools.ietf.org/html/rfc8555#section-8.3
         */
        if (challenge.type === 'http-01') {
          return result;
        }

        /**
         * https://tools.ietf.org/html/rfc8555#section-8.4
         * https://tools.ietf.org/html/draft-ietf-acme-tls-alpn-01
         */
        if (challenge.type === 'dns-01' || challenge.type === 'tls-alpn-01') {
          throw new Error(`Unsupported challenge type: ${challenge.type}`);
        }
        throw new Error(`Unable to produce key authorization, unknown challenge type: ${challenge}`);
      });
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Notify CA that challenge has been completed
   *
   * https://tools.ietf.org/html/rfc8555#section-7.5.1
   *
   * @param {object} challenge Challenge object returned by API
   * @returns {Promise<object>} Challenge
   *
   * @example Notify CA that challenge has been completed
   * ```js
   * const challenge = { ... }; // Satisfied challenge
   * const result = await client.completeChallenge(challenge);
   * ```
   */
  ;
  _proto.completeChallenge = function completeChallenge(challenge) {
    try {
      var _this11 = this;
      return _await(_this11.api.completeChallenge(challenge.url, {}), resp => _await(resp.json(), _resp$json9 => _resp$json9));
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Wait for ACME provider to verify status on a order, authorization or challenge
   *
   * https://tools.ietf.org/html/rfc8555#section-7.5.1
   *
   * @param {object} item An order, authorization or challenge object
   * @returns {Promise<object>} Valid order, authorization or challenge
   *
   * @example Wait for valid challenge status
   * ```js
   * const challenge = { ... };
   * await client.waitForValidStatus(challenge);
   * ```
   *
   * @example Wait for valid authorization status
   * ```js
   * const authz = { ... };
   * await client.waitForValidStatus(authz);
   * ```
   *
   * @example Wait for valid order status
   * ```js
   * const order = { ... };
   * await client.waitForValidStatus(order);
   * ```
   */
  ;
  _proto.waitForValidStatus = function waitForValidStatus(item) {
    try {
      var _this12 = this;
      if (!item.url) {
        throw new Error('Unable to verify status of item, URL not found');
      }
      var verifyFn = _async(abort => _await(_this12.api.apiRequest(item.url, null, [200]), resp => _await(resp.json(), _resp$json10 => {
        var respData = _resp$json10;
        _this12.log.info('Item has status:', respData.status);
        if (invalidStates.includes(respData.status)) {
          abort();
          throw new Error(formatResponseError(respData));
        } else if (pendingStates.includes(respData.status)) {
          throw new Error('Operation is pending or processing');
        } else if (validStates.includes(respData.status)) {
          return respData;
        }
        throw new Error(`Unexpected item status: ${respData.status}`);
      })));
      _this12.log.info('Waiting for valid status from', item.url, _this12.backoffOpts);
      return _await(retry(verifyFn, _this12.backoffOpts));
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Get certificate from ACME order
   *
   * https://tools.ietf.org/html/rfc8555#section-7.4.2
   *
   * @param {object} order Order object
   * @param {string} [preferredChain] Indicate which certificate chain is preferred if a CA offers multiple, by exact issuer common name, default: `null`
   * @returns {Promise<string>} Certificate
   *
   * @example Get certificate
   * ```js
   * const order = { ... }; // Previously created order
   * const certificate = await client.getCertificate(order);
   * ```
   *
   * @example Get certificate with preferred chain
   * ```js
   * const order = { ... }; // Previously created order
   * const certificate = await client.getCertificate(order, 'DST Root CA X3');
   * ```
   */
  ;
  _proto.getCertificate = function getCertificate(order, _preferredChain // TODO delete?
  ) {
    try {
      var _this13 = this;
      if (_preferredChain === void 0) {
        _preferredChain = null;
      }
      return _await(_invoke(() => {
        if (!validStates.includes(order.status)) {
          return _await(_this13.waitForValidStatus(order), _this13$waitForValidS => {
            order = _this13$waitForValidS;
          });
        }
      }, () => {
        if (!order.certificate) {
          throw new Error('Unable to download certificate, URL not found');
        }
        return _await(_this13.api.apiRequest(order.certificate, null, [200]), resp => _await(resp.text()));
        /* Handle alternate certificate chains */
        // TODO -- SHOULD WE DELETE THIS? OR IMPLEMENT utils.*
        //if (preferredChain && resp.headers.link) {
        //  const alternateLinks = util.parseLinkHeader(resp.headers.link)
        //  const alternates = await Promise.all(
        //    alternateLinks.map(async (link: string) =>
        //      this.api.apiRequest(link, null, [200])
        //    )
        //  )
        //  const certificates = [resp].concat(alternates).map((c) => c.data)
        //  return util.findCertificateChainForIssuer(certificates, preferredChain)
        //}
        /* Return default certificate chain */
      }));
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Revoke certificate
   *
   * https://tools.ietf.org/html/rfc8555#section-7.6
   *
   * @param {buffer|string} cert PEM encoded certificate
   * @param {object} [data] Additional request data
   * @returns {Promise}
   *
   * @example Revoke certificate
   * ```js
   * const certificate = { ... }; // Previously created certificate
   * const result = await client.revokeCertificate(certificate);
   * ```
   *
   * @example Revoke certificate with reason
   * ```js
   * const certificate = { ... }; // Previously created certificate
   * const result = await client.revokeCertificate(certificate, {
   *     reason: 4
   * });
   * ```
   */
  ;
  _proto.revokeCertificate = function revokeCertificate(cert, data) {
    try {
      var _this14 = this;
      if (data === void 0) {
        data = {};
      }
      data.certificate = getPemBodyAsB64u(cert);
      return _await(_this14.api.revokeCert(data), resp => _await(resp.json(), _resp$json11 => _resp$json11));
    } catch (e) {
      return Promise.reject(e);
    }
  }
  /**
   * Auto mode
   *
   * @param {object} opts
   * @param {buffer|string} opts.csr Certificate Signing Request
   * @param {function} opts.challengeCreateFn Function returning Promise triggered before completing ACME challenge
   * @param {function} opts.challengeRemoveFn Function returning Promise triggered after completing ACME challenge
   * @param {string} [opts.email] Account email address
   * @param {boolean} [opts.termsOfServiceAgreed] Agree to Terms of Service, default: `false`
   * @param {string[]} [opts.challengePriority] Array defining challenge type priority, default: `['http-01', 'dns-01']`
   * @param {string} [opts.preferredChain] Indicate which certificate chain is preferred if a CA offers multiple, by exact issuer common name, default: `null`
   * @returns {Promise<string>} Certificate
   *
   * @example Order a certificate using auto mode
   * ```js
   * const [certificateKey, certificateRequest] = await acme.crypto.createCsr({
   *     commonName: 'test.example.com'
   * });
   *
   * const certificate = await client.auto({
   *     csr: certificateRequest,
   *     email: 'test@example.com',
   *     termsOfServiceAgreed: true,
   *     challengeCreateFn: async (authz, challenge, keyAuthorization) => {
   *         // Satisfy challenge here
   *     },
   *     challengeRemoveFn: async (authz, challenge, keyAuthorization) => {
   *         // Clean up challenge here
   *     }
   * });
   * ```
   *
   * @example Order a certificate using auto mode with preferred chain
   * ```js
   * const [certificateKey, certificateRequest] = await acme.crypto.createCsr({
   *     commonName: 'test.example.com'
   * });
   *
   * const certificate = await client.auto({
   *     csr: certificateRequest,
   *     email: 'test@example.com',
   *     termsOfServiceAgreed: true,
   *     preferredChain: 'DST Root CA X3',
   *     challengeCreateFn: async () => {},
   *     challengeRemoveFn: async () => {}
   * });
   * ```
   */
  ;
  _proto.auto = function auto(opts) {
    return _auto(this, opts);
  }

  /** how verbose these logs will be */;
  _createClass(AcmeClient, [{
    key: "minLevel",
    get: function () {
      return this.log.minLevel;
    }

    /** controls how verbose these logs will be. Does not affect the level of {@link AcmeClient.api}. */,
    set: function (v) {
      this.log.minLevel = v;
    }
  }]);
  return AcmeClient;
}();

/*
 * Demonstrates using js_content to serve challenge responses.
 */
var challengeResponse = _async(r => {
  var challengeUriPrefix = '/.well-known/acme-challenge/';

  // Only support GET requests
  if (r.method !== 'GET') {
    return r.return(400, 'Bad Request');
  }

  // Here is the challenge token spec:
  // https://datatracker.ietf.org/doc/html/draft-ietf-acme-acme-07#section-8.3
  // - greater than 128 bits or ~22 base-64 encoded characters.
  //   Let's Encrypt uses a 43-character string.
  // - base64url characters only

  // Ensure we're not given a token that is too long (128 chars to be future-proof)
  if (r.uri.length > 128 + challengeUriPrefix.length) {
    return r.return(400, 'Bad Request');
  }

  // Ensure this handler is only receiving /.well-known/acme-challenge/
  // requests, and not other requests through some kind of configuration
  // mistake.
  if (!r.uri.startsWith(challengeUriPrefix)) {
    return r.return(400, 'Bad Request');
  }
  var token = r.uri.substring(challengeUriPrefix.length);

  // Token must only contain base64url chars
  if (token.match(/[^a-zA-Z0-9-_]/)) {
    return r.return(400, 'Bad Request');
  }
  try {
    return r.return(200,
    // just return the contents of the token file
    fs.readFileSync(joinPaths(acmeChallengeDir(r), token), 'utf8'));
  } catch (e) {
    return r.return(404, 'Not Found');
  }
});
/**
 * Create a new certificate Signing Request - Example implementation
 * @param r
 * @returns
 */
var createCsrHandler = _async(r => _await(createCsr({
  // EXAMPLE VALUES BELOW
  altNames: ['proxy1.f5.com', 'proxy2.f5.com'],
  commonName: 'proxy.f5.com',
  state: 'WA',
  country: 'US',
  organizationUnit: 'NGINX'
}), _ref => {
  var pkcs10Ber = _ref.pkcs10Ber,
    keys = _ref.keys;
  return _await(crypto.subtle.exportKey('pkcs8', keys.privateKey), _crypto$subtle$export2 => {
    var privkey = _crypto$subtle$export2;
    return _await(crypto.subtle.exportKey('spki', keys.publicKey), _crypto$subtle$export3 => {
      var pubkey = _crypto$subtle$export3;
      var privkeyPem = toPEM(privkey, 'PRIVATE KEY');
      var pubkeyPem = toPEM(pubkey, 'PUBLIC KEY');
      var csrPem = toPEM(pkcs10Ber, 'CERTIFICATE REQUEST');
      var result = `${privkeyPem}\n${pubkeyPem}\n${csrPem}`;
      return r.return(200, result);
    });
  });
}));
/**
 * Retrieves the cert based on the Nginx HTTP request.
 * @param {NginxHTTPRequest} r - The Nginx HTTP request object.
 * @returns {string, string} - The path and cert associated with the server name.
 */
/**
 * Demonstrates how to use generate RSA Keys and use HttpClient
 * @param r
 * @returns
 */
var acmeNewAccount = _async(r => {
  log.error('VERIFY_PROVIDER_HTTPS:', acmeVerifyProviderHTTPS(r));

  /* Generate a new RSA key pair for ACME account */
  return _call(generateKey, _generateKey => {
    var keys = _generateKey;
    // /* Create a new ACME account */
    var client = new HttpClient(acmeDirectoryURI(r), keys.privateKey);
    client.minLevel = LogLevel.Debug;
    client.setVerify(acmeVerifyProviderHTTPS(r));

    // Get Terms Of Service link from the ACME provider
    return _await(client.getMetaField('termsOfService'), tos => {
      log.info(`termsOfService: ${tos}`);
      // obtain a resource URL
      return _await(client.getResourceUrl('newAccount'), resourceUrl => {
        var payload = {
          termsOfServiceAgreed: true,
          contact: ['mailto:test@example.com']
        };
        // sends a signed request
        return _await(client.signedRequest(resourceUrl, payload), sresp => {
          var _sresp$headers = sresp.headers;
          return _await(sresp.json(), _sresp$json => {
            var respO = {
              headers: _sresp$headers,
              data: _sresp$json,
              status: sresp.status
            };
            return r.return(200, JSON.stringify(respO));
          });
        });
      });
    });
  });
});
/**
 *  Demonstrates an automated workflow to issue a new certificate for `r.variables.server_name`
 *
 * @param {NginxHTTPRequest} r Incoming request
 * @returns void
 */
var clientAutoMode = _async(r => {
  var log = new Logger('auto');
  var prefix = acmeDir(r);
  var commonName = acmeCommonName(r);
  var altNames = acmeAltNames(r);
  var pkeyPath = joinPaths(prefix, commonName + KEY_SUFFIX);
  var csrPath = joinPaths(prefix, commonName + CERTIFICATE_REQ_SUFFIX);
  var certPath = joinPaths(prefix, commonName + CERTIFICATE_SUFFIX);
  var email;
  try {
    email = getVariable(r, 'njs_acme_account_email');
  } catch (_unused) {
    return r.return(500, "Nginx variable 'njs_acme_account_email' or 'NJS_ACME_ACCOUNT_EMAIL' environment variable must be set");
  }
  var certificatePem;
  var pkeyPem;
  var renewCertificate = false;
  var certInfo;
  return _continue(_catch(() => {
    var certData = fs.readFileSync(certPath, 'utf8');
    var privateKeyData = fs.readFileSync(pkeyPath, 'utf8');
    return _await(readCertificateInfo(certData), _readCertificateInfo => {
      certInfo = _readCertificateInfo;
      var configDomains = acmeServerNames(r);
      var certDomains = certInfo.domains.altNames; // altNames includes the common name
      if (!areEqualSets(certDomains, configDomains)) {
        log.info(`Renewing certificate because the hostnames in the certificate (${certDomains.join(', ')}) do not match the configured njs_acme_server_names (${configDomains.join(',')})`);
        renewCertificate = true;
      } else {
        // Calculate the date 30 days before the certificate expiration
        var renewalThreshold = new Date(certInfo.notAfter);
        renewalThreshold.setDate(renewalThreshold.getDate() - 30);
        var currentDate = new Date();
        if (currentDate > renewalThreshold) {
          renewCertificate = true;
        } else {
          certificatePem = certData;
          pkeyPem = privateKeyData;
        }
      }
    });
  }, () => {
    renewCertificate = true;
  }), () => {
    var _exit = false;
    return _invoke(() => {
      if (renewCertificate) {
        return _await(readOrCreateAccountKey(acmeAccountPrivateJWKPath(r)), accountKey => {
          // Create a new ACME client
          var client = new AcmeClient({
            directoryUrl: acmeDirectoryURI(r),
            accountKey: accountKey
          });
          // client.api.minLevel = LogLevel.Debug; // display more logs
          client.api.setVerify(acmeVerifyProviderHTTPS(r));

          // Create a new CSR
          var params = {
            commonName,
            altNames,
            emailAddress: email
          };
          return _await(createCsr(params), csr => {
            fs.writeFileSync(csrPath, toPEM(csr.pkcs10Ber, 'CERTIFICATE REQUEST'));
            return _await(crypto.subtle.exportKey('pkcs8', csr.keys.privateKey), _crypto$subtle$export => {
              var privKey = _crypto$subtle$export;
              pkeyPem = toPEM(privKey, 'PRIVATE KEY');
              fs.writeFileSync(pkeyPath, pkeyPem);
              log.info(`Wrote Private key to ${pkeyPath}`);
              var challengePath = acmeChallengeDir(r);
              try {
                fs.mkdirSync(challengePath, {
                  recursive: true
                });
              } catch (e) {
                log.error(`Error creating directory to store challenges. Ensure the ${challengePath} directory is writable by the nginx user.`);
                var _r$return = r.return(500, 'Cannot create challenge directory');
                _exit = true;
                return _r$return;
              }
              return _await(client.auto({
                csr: Buffer.from(csr.pkcs10Ber),
                email,
                termsOfServiceAgreed: true,
                challengeCreateFn: _async((authz, challenge, keyAuthorization) => {
                  log.info('Challenge Create', {
                    authz,
                    challenge,
                    keyAuthorization
                  });
                  log.info(`Writing challenge file so nginx can serve it via .well-known/acme-challenge/${challenge.token}`);
                  ngx.log(ngx.INFO, `njs-acme: [auto] Writing challenge file so nginx can serve it via ${challengePath}/${challenge.token}`);
                  var path = joinPaths(challengePath, challenge.token);
                  fs.writeFileSync(path, keyAuthorization);
                  return _await();
                }),
                challengeRemoveFn: _async((_authz, challenge, _keyAuthorization) => {
                  var path = joinPaths(challengePath, challenge.token);
                  try {
                    fs.unlinkSync(path);
                    log.info(`removed challenge ${path}`);
                  } catch (e) {
                    log.error(`failed to remove challenge ${path}`);
                  }
                  return _await();
                })
              }), _client$auto => {
                certificatePem = _client$auto;
                return _await(readCertificateInfo(certificatePem), _readCertificateInfo2 => {
                  certInfo = _readCertificateInfo2;
                  fs.writeFileSync(certPath, certificatePem);
                  log.info(`wrote certificate to ${certPath}`);
                });
              });
            });
          });
        });
      }
    }, _result => {
      if (_exit) return _result;
      var info = {
        certificate: certInfo,
        renewedCertificate: renewCertificate
      };
      return r.return(200, JSON.stringify(info));
    });
  });
});
/**
 * Using AcmeClient to create a new account. It creates an account key if it doesn't exists
 * @param {NginxHTTPRequest} r Incoming request
 * @returns void
 */
var clientNewAccount = _async(r => _await(readOrCreateAccountKey(acmeAccountPrivateJWKPath(r)), accountKey => {
  // Create a new ACME account
  var client = new AcmeClient({
    directoryUrl: acmeDirectoryURI(r),
    accountKey: accountKey
  });
  // display more logs
  client.api.minLevel = LogLevel.Debug;
  // do not validate ACME provider cert
  client.api.setVerify(acmeVerifyProviderHTTPS(r));
  return _catch(() => _await(client.createAccount({
    termsOfServiceAgreed: true,
    contact: ['mailto:test@example.com']
  }), account => r.return(200, JSON.stringify(account))), e => {
    var errMsg = `Error creating ACME account. Error=${e}`;
    log.error(errMsg);
    return r.return(500, errMsg);
  });
}));
var KEY_SUFFIX = '.key';
var CERTIFICATE_SUFFIX = '.crt';
var CERTIFICATE_REQ_SUFFIX = '.csr';
var log = new Logger();
function js_cert(r) {
  return read_cert_or_key(r, CERTIFICATE_SUFFIX);
}

/**
 * Retrieves the key based on the Nginx HTTP request.
 * @param {NginxHTTPRequest} r - The Nginx HTTP request object.
 * @returns {string} - The path and key associated with the server name.
 */
function js_key(r) {
  return read_cert_or_key(r, KEY_SUFFIX);
}
function read_cert_or_key(r, suffix) {
  var data = '';
  var path = '';
  var prefix = acmeDir(r);
  var commonName = acmeCommonName(r);
  var zone = acmeZoneName(r);
  path = joinPaths(prefix, commonName + suffix);
  var key = ['acme', path].join(':');
  var cache = zone && ngx.shared && ngx.shared[zone];
  if (cache) {
    data = cache.get(key) || '';
    if (data) {
      return data;
    }
  }
  try {
    data = fs.readFileSync(path, 'utf8');
  } catch (e) {
    data = '';
    log.error('error reading from file:', path, `. Error=${e}`);
  }
  if (cache && data) {
    try {
      cache.set(key, data);
      log.debug(`wrote to cache: ${key} zone: ${zone}`);
    } catch (e) {
      var errMsg = `error writing to shared dict zone: ${zone}. Error=${e}`;
      log.error(errMsg);
    }
  }
  return data;
}
var index = {
  js_cert,
  js_key,
  acmeNewAccount,
  challengeResponse,
  clientNewAccount,
  clientAutoMode,
  createCsrHandler,
  LogLevel,
  Logger
};

export default index;
