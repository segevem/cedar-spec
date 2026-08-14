# DRT mismatches — run-1h-20reps-v2 (14 records)

All: Lean relational typechecker ACCEPTS; Rust `cedar-policy` validator REJECTS.

### V1 — steep-tags-sz12  (seed 1006929600, idx 77)

**Policy**
```cedar
permit(principal, action, resource) when { ((resource in d::"owner") && ("d" like "\u{8}*\u{5}:1bc*\0")) && ((resource.b).isIpv4()) };
```
**Schema**
```
entity id::d enum [e, foo, name]
entity d { b: ipaddr; baz: Set<Bool> } +tags
action "owner" appliesTo(principal:[], resource:[], context:{id: duration})
action "foo" appliesTo(principal:[], resource:[], context:{})
```
**Rust (cedar-policy):** `× for policy `policy0`, attribute `b` on entity type `id::d` not found`
**Lean (spec):** ACCEPTS (no errors)

### V2 — steep-tags-sz12  (seed 8008087600, idx 61)

**Policy**
```cedar
permit(principal, action, resource) when { (bar::baz::"baz" has name) && ((resource in bar::baz::"baz") && (resource.id)) };
```
**Schema**
```
entity foo::d::id enum [e]
entity bar::baz { id: Bool; name: decimal? }
action "b" appliesTo(principal:[], resource:[], context:{})
action "foo" appliesTo(principal:[], resource:[], context:{bar: ipaddr})
```
**Rust (cedar-policy):** `× for policy `policy0`, attribute `id` on entity type `foo::d::id` not found`
**Lean (spec):** ACCEPTS (no errors)

### V3 — steep-tags-sz12  (seed 10004784200, idx 40)

**Policy**
```cedar
permit(principal, action, resource) when { ((resource in c::"d") || (action in Action::"d")) && ((resource.b) || false) };
```
**Schema**
```
entity c { b: Bool; owner: Bool? } +tags
entity a::d { (no attrs) }
entity id::b::foo enum [bar, baz, c, foo, name, owner]
action "a" appliesTo(principal:[], resource:[], context:{e: Record})
action "d" appliesTo(principal:[], resource:[], context:{d: ipaddr; owner: datetime})
action "name" appliesTo(principal:[], resource:[], context:{id: Bool?; name: ipaddr?})
```
**Rust (cedar-policy):** `× for policy `policy0`, attribute `b` on entity type `id::b::foo` not found`
**Lean (spec):** ACCEPTS (no errors)

### V4 — steep-tags-sz12  (seed 12006526500, idx 9)

**Policy**
```cedar
permit(principal, action, resource) when { (principal in baz::baz::baz::"foo") && ((principal.a) <= (duration("0802041m0246249s"))) };
```
**Schema**
```
entity baz::baz::baz { a: duration; id: ipaddr }
entity e enum [a, b, c, d, e, name, owner]
entity foo::name enum [a, b, bar, baz, c, e, name]
action "baz" appliesTo(principal:[], resource:[], context:{})
action "owner" appliesTo(principal:[], resource:[], context:{a: Long; d: datetime})
action "c" appliesTo(principal:[], resource:[], context:{d: ipaddr; owner: Bool})
```
**Rust (cedar-policy):** `× for policy `policy0`, attribute `a` on entity type `e` not found`
**Lean (spec):** ACCEPTS (no errors)

### V5 — steep-tags-sz12  (seed 19000593500, idx 7)

**Policy**
```cedar
permit(principal, action, resource) when { (id::name::"bar" in principal) && (if (resource.getTag("priority")) then (e::"c".hasTag("foo")) else (resource.hasTag("d"))) };
```
**Schema**
```
entity id::name enum [bar, baz, d, e, name, owner]
entity e { b: duration } +tags
action "d" appliesTo(principal:[], resource:[], context:{})
action "name" appliesTo(principal:[], resource:[], context:{bar: Entity<e>?; d: datetime?; e: ipaddr?})
action "a" appliesTo(principal:[], resource:[], context:{baz: Bool?; id: decimal})
action "baz" appliesTo(principal:[], resource:[], context:{})
```
**Rust (cedar-policy):** `× for policy `policy0`, unable to guarantee safety of access to tag │ `"priority"` on entity type `id::name` help: try testing for the tag's presence with `.hasTag("priority") && ..` Error: × for policy `policy0`, unable to guarantee safety of access to tag │ `"priority"` on entity type `e` help: try testing for the tag's presence with `.hasTag("priority") && ..``
**Lean (spec):** ACCEPTS (no errors)

### V6 — steep-tags-sz20  (seed 4000449200, idx 71)

**Policy**
```cedar
permit(principal, action, resource) when { (principal in id::foo::"bar") && (principal.b) };
```
**Schema**
```
entity owner enum [a, b, baz, c, d, e, foo, id, name, owner]
entity id::foo { (no attrs) } +tags
action "e" appliesTo(principal:[], resource:[], context:{})
action "owner" appliesTo(principal:[], resource:[], context:{b: ipaddr; id: datetime; owner: Bool?})
```
**Rust (cedar-policy):** `× for policy `policy0`, attribute `b` on entity type `owner` not found`
**Lean (spec):** ACCEPTS (no errors)

### V7 — steep-tags-sz20  (seed 4000564700, idx 5)

**Policy**
```cedar
permit(principal, action, resource) when { if (principal in d::"baz") then ((41 < (-95)) && (context.c)) else ((datetime("1477-11-10T18:06:44.286Z")) <= (datetime("1587-03-15T21:16:58Z"))) };
```
**Schema**
```
entity d { (no attrs) }
entity e enum [d, name]
action "name" appliesTo(principal:[], resource:[], context:{d: String?; e: ipaddr?})
action "a" appliesTo(principal:[], resource:[], context:{})
action "owner" appliesTo(principal:[], resource:[], context:{e: duration?; name: duration?})
action "id" appliesTo(principal:[], resource:[], context:{bar: String; c: Bool})
```
**Rust (cedar-policy):** `× for policy `policy0`, attribute `c` in context for Action::"owner" not │ found help: did you mean `e`?`
**Lean (spec):** ACCEPTS (no errors)

### V8 — typeof-check-sz12  (seed 4925400, idx 74)

**Policy**
```cedar
permit(principal, action, resource) when { if (resource in foo::"c") then ((resource.getTag("priority")).isMulticast()) else ((foo::"id".hasTag("baz")) && (foo::"name".hasTag("d"))) };
```
**Schema**
```
entity foo { b: Bool?; name: Long? } +tags
entity b::d::foo enum [a, b, bar, c, d, foo, id]
action "bar" appliesTo(principal:[], resource:[], context:{})
action "e" appliesTo(principal:[], resource:[], context:{baz: ipaddr?; d: Bool?})
```
**Rust (cedar-policy):** `× for policy `policy0`, unable to guarantee safety of access to tag │ `"priority"` on entity type `b::d::foo` help: try testing for the tag's presence with `.hasTag("priority") && ..``
**Lean (spec):** ACCEPTS (no errors)

### V9 — typeof-check-sz12  (seed 1002711200, idx 68)

**Policy**
```cedar
permit(principal, action, resource) when { (resource in [d::a::b::"e"]) && ((resource.foo).isMulticast()) };
```
**Schema**
```
entity a::d::b enum [bar, baz, e, owner]
entity d::a::b { a: Set<duration>; foo: ipaddr }
action "baz" appliesTo(principal:[], resource:[], context:{})
action "b" appliesTo(principal:[], resource:[], context:{})
action "bar" appliesTo(principal:[], resource:[], context:{b: String})
```
**Rust (cedar-policy):** `× for policy `policy0`, attribute `foo` on entity type `a::d::b` not found`
**Lean (spec):** ACCEPTS (no errors)

### V10 — typeof-check-sz12  (seed 3004047200, idx 78)

**Policy**
```cedar
permit(principal, action, resource) when { if (!(principal in e::c::c::"d")) then (!(2 < 85)) else (principal.owner) };
```
**Schema**
```
entity e::c::c { owner: Bool } +tags
entity owner enum [a, b, baz, c, d, id, owner]
entity e { (no attrs) }
action "baz" appliesTo(principal:[], resource:[], context:{baz: datetime?})
action "d" appliesTo(principal:[], resource:[], context:{c: String?})
```
**Rust (cedar-policy):** `× for policy `policy0`, attribute `owner` on entity type `owner` not found`
**Lean (spec):** ACCEPTS (no errors)

### V11 — typeof-check-sz12  (seed 5003493600, idx 68)

**Policy**
```cedar
permit(principal, action, resource) when { ((d::"c" in principal) && (context.name)) || (b::"id".hasTag("d")) };
```
**Schema**
```
entity d enum [c]
entity b { bar: Long?; d: datetime }
action "d" appliesTo(principal:[], resource:[], context:{c: datetime?})
action "e" appliesTo(principal:[], resource:[], context:{c: duration?; e: datetime; name: Bool})
```
**Rust (cedar-policy):** `× for policy `policy0`, attribute `name` in context for Action::"d" not │ found help: did you mean `c`?`
**Lean (spec):** ACCEPTS (no errors)

### V12 — typeof-check-sz12  (seed 8001289800, idx 66)

**Policy**
```cedar
permit(principal, action, resource) when { (!(!(!(resource in principal)))) || ((resource.owner) <= (principal.owner)) };
```
**Schema**
```
entity c::a { b: Long; owner: datetime }
entity b::b::name enum [bar, baz, c, foo, id, name]
action "baz" appliesTo(principal:[], resource:[], context:{id: Entity<name>?})
action "id" appliesTo(principal:[], resource:[], context:{})
action "bar" appliesTo(principal:[], resource:[], context:{})
```
**Rust (cedar-policy):** `× for policy `policy0`, attribute `owner` on entity type `b::b::name` not │ found`
**Lean (spec):** ACCEPTS (no errors)

### V13 — typeof-check-sz12  (seed 11001851400, idx 26)

**Policy**
```cedar
permit(principal, action, resource) when { (principal in a::"id") && (!(!(principal.foo))) };
```
**Schema**
```
entity name::a::baz enum [a, c, foo]
entity baz { owner: decimal }
entity foo enum [bar, name]
entity id enum [a, b, baz, d, id, owner]
entity a { foo: Bool }
entity bar { b: Set<Long> }
action "id" appliesTo(principal:[], resource:[], context:{id: Long})
action "c" appliesTo(principal:[], resource:[], context:{foo: Record})
action "d" appliesTo(principal:[], resource:[], context:{foo: String; owner: Record; bar: datetime})
```
**Rust (cedar-policy):** `× for policy `policy0`, attribute `foo` on entity type `name::a::baz` not │ found`
**Lean (spec):** ACCEPTS (no errors)

### V14 — typeof-check-sz20  (seed 4000365800, idx 91)

**Policy**
```cedar
permit(principal, action, resource) when { ((foo::c::"bar" in principal) || false) && (!((duration("-068697694966d")) <= (context.e))) };
```
**Schema**
```
entity e::e::id { (no attrs) }
entity foo::c enum [bar, baz, d]
action "c" appliesTo(principal:[], resource:[], context:{bar: duration; id: Long?})
action "owner" appliesTo(principal:[], resource:[], context:{b: Record?; a: duration?; c: ipaddr?})
action "name" appliesTo(principal:[], resource:[], context:{})
action "a" appliesTo(principal:[], resource:[], context:{a: Set<duration>?})
action "baz" appliesTo(principal:[], resource:[], context:{bar: datetime?; e: duration})
```
**Rust (cedar-policy):** `× for policy `policy0`, attribute `e` in context for Action::"a" not found help: did you mean `a`?`
**Lean (spec):** ACCEPTS (no errors)
