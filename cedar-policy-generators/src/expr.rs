/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use crate::abac::{
    AttrValue, AvailableExtensionFunctions, ConstantPool, QualifiedType, Type, UnknownPool,
};
use crate::err::{while_doing, Error, Result};
use crate::hierarchy::{generate_uid_with_type, Hierarchy};
use crate::schema_gen::SchemaGen;
use crate::settings::ABACSettings;
use crate::size_hint_utils::{size_hint_for_choose, size_hint_for_range, size_hint_for_ratio};
use crate::types::TypeGenerator;
use crate::{accum, gen, gen_inner, uniform};
use arbitrary::{Arbitrary, MaxRecursionReached, Unstructured};
use cedar_policy_core::ast;
use indexmap::IndexMap;
use smol_str::SmolStr;
use std::collections::BTreeMap;

/// Struct for generating expressions
#[derive(Debug)]
pub struct ExprGenerator<'a> {
    /// Schema for generated expressions to conform to
    pub schema: &'a dyn SchemaGen,
    /// General settings for ABAC generation, many of which affect expression generation
    pub settings: &'a ABACSettings,
    /// Constant pool to use when needed
    pub constant_pool: &'a ConstantPool,
    /// Unknown pool to use when needed
    pub unknown_pool: &'a UnknownPool,
    /// data on available extension functions
    pub ext_funcs: &'a AvailableExtensionFunctions,
    /// If this is present, any literal UIDs included in generated `Expr`s will
    /// (usually) exist in the hierarchy.
    pub hierarchy: Option<&'a Hierarchy>,
}

impl<'a> ExprGenerator<'a> {
    fn as_type_gen(&self) -> TypeGenerator<'a> {
        TypeGenerator {
            schema: self.schema,
            constant_pool: self.constant_pool,
            settings: self.settings,
        }
    }
}

impl ExprGenerator<'_> {
    /// get a (fully general) arbitrary expression conforming to the schema, but
    /// no attempt to match types.
    ///
    /// `max_depth`: maximum size (i.e., depth) of the expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    pub fn generate_expr(
        &mut self,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        if max_depth == 0 {
            // no recursion allowed: just generate a literal
            self.generate_literal_or_var(u)
        } else {
            gen!(u,
            2 => {
                // a literal or variable
                self.generate_literal_or_var(u)
            },
            1 => {
                // == expression
                Ok(ast::Expr::is_eq(
                    self.generate_expr(max_depth - 1, u)?,
                    self.generate_expr(max_depth - 1, u)?,
                ))
            },
            1 => {
                // not expression
                Ok(ast::Expr::not(self.generate_expr(max_depth - 1, u)?))
            },
            1 => {
                // any other expression
                gen!(u,
                    2 => Ok(ast::Expr::ite(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    2 => Ok(ast::Expr::and(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    2 => Ok(ast::Expr::or(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::less(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::lesseq(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::greater(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::greatereq(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::add(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::sub(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::mul(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => {
                        // negation expression
                        Ok(ast::Expr::neg(self.generate_expr(max_depth - 1, u)?))
                    },
                    6 => Ok(ast::Expr::is_in(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::contains(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::contains_all(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::contains_any(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::is_empty(
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    2 => {
                        if self.settings.enable_like {
                            Ok(ast::Expr::like(
                                self.generate_expr(max_depth - 1, u)?,
                                self.constant_pool.arbitrary_pattern_literal(u)?,
                            ))
                        } else {
                            Err(Error::LikeDisabled)
                        }
                    },
                    1 => {
                            Ok(ast::Expr::is_entity_type(
                                self.generate_expr(max_depth - 1, u)?,
                                self.schema.arbitrary_entity_type(u)?,
                            ))
                    },
                    1 => {
                        let mut l = Vec::new();
                        u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                            l.push(self.generate_expr(max_depth - 1, u)?);
                            Ok(std::ops::ControlFlow::Continue(()))
                        })?;
                        Ok(ast::Expr::set(l))
                    },
                    1 => {
                        let mut r = IndexMap::new();
                        u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                            let attr_name = self.schema.arbitrary_attr(u)?;
                            r.insert(
                                attr_name,
                                self.generate_expr(max_depth - 1, u)?,
                            );
                            Ok(std::ops::ControlFlow::Continue(()))
                        })?;
                        Ok(ast::Expr::record(r).expect("can't have duplicate keys because `r` was already a HashMap"))
                    },
                    1 => {
                        let func = self.ext_funcs.arbitrary_all(u)?;
                        let arity = if !self.settings.enable_arbitrary_func_call
                            || u.ratio::<u8>(9, 10)?
                        {
                            // 90% of the time respect the correct arity, but sometimes don't
                            func.parameter_types.len()
                        } else {
                            u.int_in_range::<usize>(0..=4)?
                        };
                        let fn_name = if !self.settings.enable_arbitrary_func_call
                            || u.ratio::<u8>(9, 10)?
                        {
                            // 90% of the time choose an existing extension function, but sometimes don't
                            func.name.clone()
                        } else {
                            u.arbitrary()?
                        };
                        Ok(ast::Expr::call_extension_fn(
                            fn_name,
                            (0..arity)
                                .map(|_| self.generate_expr(max_depth - 1, u))
                                .collect::<Result<_>>()?,
                        ))
                    },
                    7 => {
                        let attr_name = gen!(u,
                            1 => {
                                let s: String = u.arbitrary()?;
                                SmolStr::from(s)
                            },
                            6 => self.schema.arbitrary_attr(u)?);
                        let e = self.generate_expr(max_depth - 1, u)?;
                        // We should be able to have an arbitrary expression
                        // as the base of an `GetAttr` operation.
                        // However, in one case this will fail to parse
                        // after being pretty-printed: the case where the
                        // base is a string literal (e.g.,
                        // "c"["attr_name"]).
                        // So when we get a string lit, compose a record out
                        // of it to recover gracefully.
                        let e = if let ast::ExprKind::Lit(ast::Literal::String(ref s)) =
                            e.expr_kind()
                        {
                            ast::Expr::record([((s).clone(), e)])
                                .expect("can't have duplicate keys because there is only one key")
                        } else {
                            e
                        };
                        Ok(ast::Expr::get_attr(e, attr_name))
                    },
                    4 => {
                        let attr_name = uniform!(u,
                           self.schema.arbitrary_attr(u)?,
                            {
                                let s: String = u.arbitrary()?;
                                SmolStr::from(s)
                            });
                        Ok(ast::Expr::has_attr(
                            self.generate_expr(max_depth - 1, u)?,
                            attr_name,
                        ))
                    },
                    4 => {
                        let tag_name = uniform!(u,
                            self.generate_expr(max_depth - 1, u)?,
                            ast::Expr::val(self.schema.arbitrary_attr(u)?)
                        );
                        let e = self.generate_expr(max_depth - 1, u)?;
                        Ok(ast::Expr::has_tag(e, tag_name))
                    }
                )
            })
        }
    }

    /// get an arbitrary expression of a given type conforming to the schema
    ///
    /// `max_depth`: maximum size (i.e., depth) of the expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    pub fn generate_expr_for_type(
        &self,
        target_type: &Type,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        if self.should_generate_unknown(max_depth, u)? {
            let v = self.generate_value_for_type(target_type, max_depth, u)?;
            let name = self.unknown_pool.alloc(target_type.clone(), v);
            let unknown_type: Option<ast::Type> = target_type.clone().try_into().ok();
            match unknown_type {
                Some(ty) => Ok(ast::Expr::unknown(ast::Unknown::new_with_type(name, ty))),
                None => Ok(ast::Expr::unknown(ast::Unknown::new_untyped(name))),
            }
        } else {
            match target_type {
                Type::Bool => {
                    if max_depth == 0 || u.len() < 10 {
                        self.generate_expr_for_type_structurally_recursive(target_type, u)
                    } else {
                        gen!(u,
                        // bool literal
                        2 => Ok(ast::Expr::val(u.arbitrary::<bool>()?)),
                        // == expression, where types on both sides match
                        5 => {
                            let ty = self.as_type_gen().generate_type(max_depth, u)?;
                            Ok(ast::Expr::is_eq(
                                self.generate_expr_for_type(&ty, max_depth - 1, u)?,
                                self.generate_expr_for_type(&ty, max_depth - 1, u)?,
                            ))
                        },
                        // == expression, where types do not match
                        2 => {
                            let ty1 = self.as_type_gen().generate_type(max_depth, u)?;
                            let ty2 = self.as_type_gen().generate_type(max_depth, u)?;
                            Ok(ast::Expr::is_eq(
                                self.generate_expr_for_type(
                                    &ty1,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.generate_expr_for_type(
                                    &ty2,
                                    max_depth - 1,
                                    u,
                                )?,
                            ))
                        },
                        // not expression
                        5 => Ok(ast::Expr::not(self.generate_expr_for_type(
                            &Type::bool(),
                            max_depth - 1,
                            u,
                        )?)),
                        // && expression
                        5 => Ok(ast::Expr::and(
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // || expression
                        5 => Ok(ast::Expr::or(
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // Binary comparisons expressions (>, >=, <, and <=)
                        4 => {
                            let cmp_ty = uniform!(u,
                                Type::long(),
                                Type::datetime(),
                                Type::duration()
                            );
                            let cmp_op = uniform!(u,
                                ast::Expr::greater,
                                ast::Expr::greatereq,
                                ast::Expr::less,
                                ast::Expr::lesseq
                            );
                            Ok(cmp_op(
                                self.generate_expr_for_type(&cmp_ty, max_depth - 1, u)?,
                                self.generate_expr_for_type(&cmp_ty, max_depth - 1, u)?,
                            ))
                        },
                        // in expression, non-set form
                        11 => {
                            let ety1 = self.schema.arbitrary_entity_type(u)?;
                            let ety2 = self.schema.arbitrary_entity_type(u)?;
                            Ok(ast::Expr::is_in(
                            self.generate_expr_for_type(
                                &Type::Entity(ety1.clone()),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::Entity(ety2.clone()),
                                max_depth - 1,
                                u,
                            )?,
                        ))},
                        // in expression, set form
                        2 => {
                            let ety1 = self.schema.arbitrary_entity_type(u)?;
                            let ety2 = self.schema.arbitrary_entity_type(u)?;
                            Ok(ast::Expr::is_in(
                            self.generate_expr_for_type(
                                &Type::Entity(ety1.clone()),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                               &Type::set_of(Type::Entity(ety2.clone())),
                                max_depth - 1,
                                u,
                            )?,
                        ))},
                        // contains() on a set
                        2 => {
                            let element_ty = self.as_type_gen().generate_type(max_depth, u)?;
                            let element = self.generate_expr_for_type(
                                &element_ty,
                                max_depth - 1,
                                u,
                            )?;
                            let set = self.generate_expr_for_type(
                                &Type::set_of(element_ty),
                                max_depth - 1,
                                u,
                            )?;
                            Ok(ast::Expr::contains(set, element))
                        },
                        // containsAll()
                        1 => Ok(ast::Expr::contains_all(
                            // doesn't require the input sets to have the same element type
                            self.generate_expr_for_type(
                                &Type::set_of(self.as_type_gen().generate_type(max_depth, u)?),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::set_of(self.as_type_gen().generate_type(max_depth, u)?),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // containsAny()
                        1 => Ok(ast::Expr::contains_any(
                            // doesn't require the input sets to have the same element type
                            self.generate_expr_for_type(
                                &Type::set_of(self.as_type_gen().generate_type(max_depth, u)?),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::set_of(self.as_type_gen().generate_type(max_depth, u)?),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // isEmpty()
                        1 => Ok(ast::Expr::is_empty(
                            self.generate_expr_for_type(
                                &Type::set_of(self.as_type_gen().generate_type(max_depth, u)?),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // like
                        2 => {
                            if self.settings.enable_like {
                                Ok(ast::Expr::like(
                                    self.generate_expr_for_type(
                                        &Type::string(),
                                        max_depth - 1,
                                        u,
                                    )?,
                                    self.constant_pool.arbitrary_pattern_literal(u)?,
                                ))
                            } else {
                                Err(Error::LikeDisabled)
                            }
                        },
                        // is
                        2 => {
                            let ety_l = self.schema.arbitrary_entity_type(u)?;
                            let ety_r = self.schema.arbitrary_entity_type(u)?;
                                Ok(ast::Expr::is_entity_type(
                                    self.generate_expr_for_type(
                                        &Type::Entity(ety_l),
                                        max_depth - 1,
                                        u,
                                    )?,
                                    ety_r,
                                ))
                        },
                        // has expression on an entity, for a (possibly optional) attribute the entity does have in the schema
                        2 => {
                            let ety = self.schema.arbitrary_entity_type(u)?;
                            let attr = self.schema.arbitrary_attr_of_entity_type(&ety, u)?;
                            Ok(ast::Expr::has_attr(
                                self.generate_expr_for_type(
                                    &Type::Entity(ety),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr,
                            ))
                        },
                        // has expression on an entity, for an arbitrary attribute name
                        1 => Ok(ast::Expr::has_attr(
                            self.generate_expr_for_type(
                                &Type::Entity(self.schema.arbitrary_entity_type(u)?),
                                max_depth - 1,
                                u,
                            )?,
                            self.constant_pool.arbitrary_string_constant(u)?,
                        )),
                        // hasTag expression on an entity, for an arbitrary tag name
                        1 => Ok(ast::Expr::has_tag(
                            self.generate_expr_for_type(
                                &Type::Entity(self.schema.arbitrary_entity_type(u)?),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::string(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // has expression on a record
                        2 => Ok(ast::Expr::has_attr(
                            self.generate_expr_for_type(
                                &self.as_type_gen().generate_record_type(max_depth, u)?,
                                max_depth - 1,
                                u,
                            )?,
                            self.constant_pool.arbitrary_string_constant(u)?,
                        )),
                        // extension function that returns bool
                        2 => self.generate_ext_func_call_for_type(&Type::Bool, max_depth - 1, u),
                        // if-then-else expression, where both arms are bools
                        5 => self.generate_ite_for_type(&Type::Bool, max_depth, u),
                        // getting an attr (on an entity) with type bool
                        1 => self.generate_get_entity_attr_for_type(&Type::Bool, max_depth, u),
                        // getting an attr (on a record) with type bool
                        1 => self.generate_get_record_attr_for_type(&Type::Bool, max_depth, u),
                        // getting an entity tag with type bool
                        1 => self.generate_get_tag_for_type(&Type::Bool, max_depth, u))
                    }
                }
                Type::Long => {
                    if max_depth == 0 || u.len() < 10 {
                        self.generate_expr_for_type_structurally_recursive(target_type, u)
                    } else {
                        gen!(u,
                        // int literal. weighted highly because all the other choices
                        // are recursive, and we don't want a scenario where we have,
                        // say, a 90% chance to recurse every time
                        16 => Ok(ast::Expr::val(
                            self.constant_pool.arbitrary_int_constant(u)?,
                        )),
                        // + expression
                        1 => Ok(ast::Expr::add(
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // - expression
                        1 => Ok(ast::Expr::sub(
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // * expression
                        1 => Ok(ast::Expr::mul(
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // negation expression
                        1 => Ok(ast::Expr::neg(self.generate_expr_for_type(
                            &Type::long(),
                            max_depth - 1,
                            u,
                        )?)),
                        // extension function that returns a long
                        1 => self.generate_ext_func_call_for_type(&Type::Long, max_depth - 1, u),
                        // if-then-else expression, where both arms are longs
                        5 => self.generate_ite_for_type(&Type::Long, max_depth, u),
                        // getting an attr (on an entity) with type long
                        4 => self.generate_get_entity_attr_for_type(&Type::Long, max_depth, u),
                        // getting an attr (on a record) with type long
                        4 => self.generate_get_record_attr_for_type(&Type::Long, max_depth, u),
                        // getting an entity tag with type long
                        3 => self.generate_get_tag_for_type(&Type::Long, max_depth, u))
                    }
                }
                Type::String => {
                    if max_depth == 0 || u.len() < 10 {
                        self.generate_expr_for_type_structurally_recursive(target_type, u)
                    } else {
                        gen!(u,
                        // string literal. weighted highly because all the other choices
                        // are recursive, and we don't want a scenario where we have, say,
                        // a 90% chance to recurse every time
                        16 => Ok(ast::Expr::val(
                            self.constant_pool.arbitrary_string_constant(u)?,
                        )),
                        // if-then-else expression, where both arms are strings
                        5 => self.generate_ite_for_type(&Type::String, max_depth, u),
                        // extension function that returns a string
                        1 => self.generate_ext_func_call_for_type(&Type::String, max_depth - 1, u),
                        // getting an attr (on an entity) with type string
                        4 => self.generate_get_entity_attr_for_type(&Type::String, max_depth, u),
                        // getting an attr (on a record) with type string
                        4 => self.generate_get_record_attr_for_type(&Type::String, max_depth, u),
                        // getting an entity tag with type string
                        3 => self.generate_get_tag_for_type(&Type::String, max_depth, u))
                    }
                }
                Type::Set(target_element_ty) => {
                    if max_depth == 0 || u.len() < 10 {
                        self.generate_expr_for_type_structurally_recursive(target_type, u)
                    } else {
                        gen!(u,
                        // set literal
                        6 => {
                            let mut l = Vec::new();
                            u.arbitrary_loop(
                                Some(0),
                                Some(self.settings.max_width as u32),
                                |u| {
                                    l.push(self.generate_expr_for_type(
                                        target_element_ty,
                                        max_depth - 1,
                                        u,
                                    )?);
                                    Ok(std::ops::ControlFlow::Continue(()))
                                },
                            )?;
                            Ok(ast::Expr::set(l))
                        },
                        // if-then-else expression, where both arms are (appropriate) sets
                        2 => self.generate_ite_for_type(target_type, max_depth, u),
                        // extension function that returns an (appropriate) set
                        1 => self.generate_ext_func_call_for_type(target_type, max_depth - 1, u),
                        // getting an attr (on an entity) with the appropriate set type
                        4 => self.generate_get_entity_attr_for_type(target_type, max_depth, u),
                        // getting an attr (on a record) with the appropriate set type
                        3 => self.generate_get_record_attr_for_type(target_type, max_depth, u),
                        // getting an entity tag with the appropriate set type
                        3 => self.generate_get_tag_for_type(target_type, max_depth, u))
                    }
                }
                Type::Record(m) => {
                    if max_depth == 0 || u.len() < 10 {
                        self.generate_expr_for_type_structurally_recursive(target_type, u)
                    } else {
                        gen!(u,
                        // record literal
                        2 => {
                            let mut r = IndexMap::new();
                            for (a, qt) in m {
                                if qt.required || u.ratio(1, 2)?{
                                    r.insert(a.clone(), self.generate_expr_for_type(&qt.ty, max_depth-1, u)?);
                                }
                            }
                            Ok(ast::Expr::record(r).expect("can't have duplicate keys because `r` was already a HashMap"))
                        },
                        // if-then-else expression, where both arms are records
                        2 => self.generate_ite_for_type(target_type, max_depth, u),
                        // extension function that returns a record
                        1 => self.generate_ext_func_call_for_type(target_type, max_depth - 1, u,),
                        // getting an attr (on an entity) with type record
                        4 => self.generate_get_entity_attr_for_type(target_type, max_depth, u),
                        // getting an attr (on a record) with type record
                        3 => self.generate_get_record_attr_for_type(target_type, max_depth, u),
                        // getting an entity tag with type record
                        3 => self.generate_get_tag_for_type(target_type, max_depth, u),
                        // `context`
                        1 => Ok(ast::Expr::var(ast::Var::Context)))
                    }
                }
                Type::Entity(ety) => {
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed, so, just do `principal`, `action`, or `resource`
                        self.generate_expr_for_type_structurally_recursive(target_type, u)
                    } else {
                        gen!(u,
                        // UID literal, that exists
                        11 => Ok(ast::Expr::val(self.arbitrary_uid_with_type(ety, u)?)),
                        // UID literal, that doesn't exist
                        2 => Ok(ast::Expr::val(u.arbitrary::<ast::EntityUID>()?)),
                        // `principal`
                        6 => Ok(ast::Expr::var(ast::Var::Principal)),
                        // `action`
                        6 => Ok(ast::Expr::var(ast::Var::Action)),
                        // `resource`
                        6 => Ok(ast::Expr::var(ast::Var::Resource)),
                        // if-then-else expression, where both arms are entities
                        2 => self.generate_ite_for_type(target_type, max_depth, u),
                        // extension function that returns an entity
                        1 => self.generate_ext_func_call_for_type(target_type, max_depth - 1, u,),
                        // getting an attr (on an entity) with type entity
                        6 => self.generate_get_entity_attr_for_type(target_type, max_depth, u),
                        // getting an attr (on a record) with type entity
                        5 => self.generate_get_record_attr_for_type(target_type, max_depth, u),
                        // getting an entity tag with type entity
                        5 => self.generate_get_tag_for_type(target_type, max_depth, u))
                    }
                }
                Type::IPAddr | Type::Decimal | Type::DateTime | Type::Duration => {
                    if max_depth == 0 || u.len() < 10 {
                        self.generate_expr_for_type_structurally_recursive(target_type, u)
                    } else {
                        gen!(u,
                        // if-then-else expression, where both arms are extension types
                        2 => self.generate_ite_for_type(target_type, max_depth, u),
                        // extension function that returns an extension type
                        9 => self.generate_ext_func_call_for_type(target_type, max_depth - 1, u,),
                        // getting an attr (on an entity) with extension type
                        2 => self.generate_get_entity_attr_for_type(target_type, max_depth, u),
                        // getting an attr (on a record) with extension type
                        2 => self.generate_get_record_attr_for_type(target_type, max_depth, u),
                        // getting an entity tag with extension type
                        5 => self.generate_get_tag_for_type(target_type, max_depth, u))
                    }
                }
            }
        }
    }

    /// Get an arbitrary expression of a given type conforming to the schema by
    /// structural recursion on the type. This function is guaranteed to
    /// terminate regardless of the bytes provided by `u`.
    ///
    /// To ensure this, it may call it's self recursively, but only on a type
    /// obtained from destructing `target_type`. It may not call `generate_expr_for_type`.
    fn generate_expr_for_type_structurally_recursive(
        &self,
        target_type: &Type,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        match target_type {
            Type::Bool => Ok(ast::Expr::val(u.arbitrary::<bool>()?)),
            Type::Long => Ok(ast::Expr::val(
                self.constant_pool.arbitrary_int_constant(u)?,
            )),
            Type::String => Ok(ast::Expr::val(
                self.constant_pool.arbitrary_string_constant(u)?,
            )),
            Type::Set(el_ty) => {
                let mut l = Vec::new();
                u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                    l.push(self.generate_expr_for_type_structurally_recursive(el_ty, u)?);
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(ast::Expr::set(l))
            }
            Type::Record(m) => match u.int_in_range(0..=3)? {
                0 => Ok(ast::Expr::var(ast::Var::Context)),
                _ => {
                    let r = m
                        .iter()
                        .filter_map(|(a, qt)| {
                            qt.required.then(|| {
                                self.generate_expr_for_type_structurally_recursive(&qt.ty, u)
                                    .map(|e| (a.clone(), e))
                            })
                        })
                        .collect::<Result<IndexMap<_, _>>>()?;
                    Ok(ast::Expr::record(r)
                        .expect("can't have duplicate keys because `r` was already a HashMap"))
                }
            },
            Type::Entity(ety) => match u.int_in_range(0..=3)? {
                0 => Ok(ast::Expr::var(ast::Var::Principal)),
                1 => Ok(ast::Expr::var(ast::Var::Action)),
                2 => Ok(ast::Expr::var(ast::Var::Resource)),
                _ => Ok(ast::Expr::val(self.arbitrary_uid_with_type(ety, u)?)),
            },
            Type::IPAddr | Type::Decimal | Type::DateTime | Type::Duration => self
                .arbitrary_ext_constructor_call_for_type(
                    target_type,
                    ast::Expr::val,
                    ast::Expr::call_extension_fn,
                    u,
                ),
        }
    }

    fn generate_ite_for_type(
        &self,
        target_type: &Type,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        Ok(ast::Expr::ite(
            self.generate_expr_for_type(&Type::bool(), max_depth - 1, u)?,
            self.generate_expr_for_type(target_type, max_depth - 1, u)?,
            self.generate_expr_for_type(target_type, max_depth - 1, u)?,
        ))
    }

    fn generate_get_entity_attr_for_type(
        &self,
        target_type: &Type,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        let (entity_type, attr_name) = self.schema.arbitrary_attr_for_type(target_type, u)?;
        Ok(ast::Expr::get_attr(
            self.generate_expr_for_type(&Type::Entity(entity_type.clone()), max_depth - 1, u)?,
            attr_name.clone(),
        ))
    }

    fn generate_get_record_attr_for_type(
        &self,
        target_type: &Type,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
        Ok(ast::Expr::get_attr(
            self.generate_expr_for_type(
                &record_type_with_attr(attr_name.clone(), target_type.clone()),
                max_depth - 1,
                u,
            )?,
            attr_name,
        ))
    }

    fn generate_get_tag_for_type(
        &self,
        target_type: &Type,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        let entity_type = self
            .schema
            .arbitrary_entity_type_with_tag_type(target_type, u)?;
        Ok(ast::Expr::get_tag(
            self.generate_expr_for_type(&Type::Entity(entity_type), max_depth - 1, u)?,
            self.generate_expr_for_type(&Type::String, max_depth - 1, u)?,
        ))
    }

    /// get an arbitrary constant of a given type, as an expression.
    #[allow(dead_code)]
    fn generate_const_expr_for_type(
        &self,
        target_type: &Type,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        match target_type {
            Type::Bool => Ok(ast::Expr::val(u.arbitrary::<bool>()?)),
            Type::Long => Ok(ast::Expr::val(
                self.constant_pool.arbitrary_int_constant(u)?,
            )),
            Type::String => Ok(ast::Expr::val(
                self.constant_pool.arbitrary_string_constant(u)?,
            )),
            Type::Set(el_ty) => {
                let mut l = Vec::new();
                u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                    l.push(self.generate_const_expr_for_type(el_ty, u)?);
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(ast::Expr::set(l))
            }
            Type::Record(m) => {
                let mut r = IndexMap::new();
                for (a, qt) in m {
                    if qt.required || u.ratio(1, 2)? {
                        r.insert(a.clone(), self.generate_const_expr_for_type(&qt.ty, u)?);
                    }
                }
                Ok(ast::Expr::record(r)
                    .expect("can't have duplicate keys because `r` was already a HashMap"))
            }
            Type::Entity(ety) => {
                gen!(u,
                // UID literal, that exists
                3 => Ok(ast::Expr::val(self.arbitrary_uid_with_type(ety, u)?)),
                // UID literal, that doesn't exist
                1 => Ok(ast::Expr::val(u.arbitrary::<ast::EntityUID>()?))
                )
            }
            Type::IPAddr | Type::Decimal | Type::DateTime | Type::Duration => {
                unimplemented!("constant expression of type ipaddr or decimal")
            }
        }
    }

    /// internal helper function: get an extension-function-call expression that
    /// returns the given type
    ///
    /// `max_depth`: maximum depth of each argument expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    fn generate_ext_func_call_for_type(
        &self,
        target_type: &Type,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        let func = self.ext_funcs.arbitrary_for_type(target_type, u)?;
        assert_eq!(&func.return_ty, target_type);
        let mut args: Vec<ast::Expr> = func
            .parameter_types
            .iter()
            .map(|param_ty| self.generate_expr_for_type(param_ty, max_depth, u))
            .collect::<Result<_>>()?;
        if self.settings.enable_arbitrary_func_call && u.ratio::<u8>(1, 20)? {
            let last_param_ty = func
                .parameter_types
                .last()
                .expect("All extension functions accept at least one argument.");
            u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                args.push(self.generate_expr_for_type(last_param_ty, max_depth, u)?);
                Ok(std::ops::ControlFlow::Continue(()))
            })?;
        }
        Ok(ast::Expr::call_extension_fn(func.name.clone(), args))
    }

    /// Generate a call for an extension constructor producing `target_type`.
    /// This functions is used to produce either `AttrValue`
    /// extension constructors, or `Expr` extension constructors, by passing `mk_str`
    /// and `mk_ext` functions that build string literals and extension function
    /// calls for these types.
    fn arbitrary_ext_constructor_call_for_type<E>(
        &self,
        target_type: &Type,
        mk_str: fn(SmolStr) -> E,
        mk_ext: fn(ast::Name, Vec<E>) -> E,
        u: &mut Unstructured<'_>,
    ) -> Result<E> {
        let func = self
            .ext_funcs
            .arbitrary_constructor_for_type(target_type, u)?;
        assert_eq!(&func.return_ty, target_type);
        assert!(
            func.name.is_unqualified(),
            "Expected that all extension functions would be unqualified, but {func_name} is not.",
            func_name = func.name
        );
        let name_as_ref = func.name.basename_as_ref().as_ref();
        let args = match name_as_ref {
            "ip" => vec![mk_str(self.constant_pool.arbitrary_ip_str(u)?)],
            "decimal" => vec![mk_str(self.constant_pool.arbitrary_decimal_str(u)?)],
            "datetime" => vec![mk_str(self.constant_pool.arbitrary_datetime_str(u)?)],
            "offset" => {
                let base_datetime_str = self.constant_pool.arbitrary_datetime_str(u)?;
                let offset_duration_str = self.constant_pool.arbitrary_duration_str(u)?;
                vec![
                    mk_ext(
                        ast::Name::parse_unqualified_name("datetime")
                            .expect("should be a valid identifier"),
                        vec![mk_str(base_datetime_str)],
                    ),
                    mk_ext(
                        ast::Name::parse_unqualified_name("duration")
                            .expect("should be a valid identifier"),
                        vec![mk_str(offset_duration_str)],
                    ),
                ]
            }
            "duration" => vec![mk_str(self.constant_pool.arbitrary_duration_str(u)?)],
            _ => unreachable!("unhandled extension constructor {name_as_ref}"),
        };
        assert_eq!(
            args.len(),
            func.parameter_types.len(),
            "Generated wrong number of args for {name_as_ref} extension constructor"
        );

        Ok(mk_ext(func.name.clone(), args))
    }

    /// get an AttrValue of the given type which conforms to this schema
    ///
    /// If `hierarchy` is present, any literal UIDs included in the AttrValue
    /// will (usually) exist in the hierarchy.
    ///
    /// `max_depth`: maximum depth of the attribute value expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    pub fn generate_attr_value_for_type(
        &self,
        target_type: &Type,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<AttrValue> {
        match target_type {
            Type::Bool => {
                // the only valid bool-typed attribute value is a bool literal
                Ok(AttrValue::BoolLit(u.arbitrary()?))
            }
            Type::Long => {
                // the only valid long-typed attribute value is an int literal
                Ok(AttrValue::IntLit(
                    self.constant_pool.arbitrary_int_constant(u)?,
                ))
            }
            Type::String => {
                // the only valid string-typed attribute value is a string literal
                Ok(AttrValue::StringLit(
                    self.constant_pool.arbitrary_string_constant(u)?,
                ))
            }
            Type::Entity(ety) => {
                // the only valid entity-typed attribute value is a UID literal
                Ok(AttrValue::UIDLit(self.arbitrary_uid_with_type(ety, u)?))
            }
            Type::IPAddr | Type::Decimal | Type::DateTime | Type::Duration => {
                // the only valid extension-typed attribute value is a call of an extension constructor with return the type returned
                if max_depth == 0 {
                    return Err(Error::TooDeep);
                }
                self.arbitrary_ext_constructor_call_for_type(
                    target_type,
                    AttrValue::StringLit,
                    |fn_name, args| AttrValue::ExtFuncCall { fn_name, args },
                    u,
                )
            }
            Type::Set(target_element_ty) => {
                // the only valid Set-typed attribute value is a set literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty set
                    Ok(AttrValue::Set(vec![]))
                } else {
                    let mut l = Vec::new();
                    u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                        l.push(self.generate_attr_value_for_type(
                            target_element_ty,
                            max_depth - 1,
                            u,
                        )?);
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    Ok(AttrValue::Set(l))
                }
            }
            Type::Record(m) => {
                let mut r = IndexMap::new();
                // the only valid Record-typed attribute value is a record literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty record
                    Ok(AttrValue::Record(IndexMap::new()))
                } else {
                    for (attr, qt) in m {
                        if qt.required || u.ratio(1, 2)? {
                            r.insert(
                                attr.clone(),
                                self.generate_attr_value_for_type(&qt.ty, max_depth - 1, u)?,
                            );
                        }
                    }
                    Ok(AttrValue::Record(r))
                }
            }
        }
    }

    /// size hint for arbitrary_attr_value_for_type()
    #[allow(dead_code)]
    pub fn generate_attr_value_for_type_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        arbitrary::size_hint::try_recursion_guard(depth, |depth| {
            Ok(arbitrary::size_hint::and(
                size_hint_for_range(0, 7),
                arbitrary::size_hint::or_all(&[
                    <bool as Arbitrary>::size_hint(depth),
                    ConstantPool::arbitrary_int_constant_size_hint(depth),
                    ConstantPool::arbitrary_string_constant_size_hint(depth),
                    ExprGenerator::generate_uid_size_hint(depth),
                    arbitrary::size_hint::and_all(&[
                        AvailableExtensionFunctions::arbitrary_constructor_for_type_size_hint(
                            depth,
                        ),
                        size_hint_for_ratio(9, 10),
                        size_hint_for_range(0, 4),
                        Self::generate_attr_value_for_type_size_hint(depth)?,
                    ]),
                    (1, None), // not sure how to hint for arbitrary_loop()
                    (1, None), // not sure how to hint for arbitrary_loop()
                    (1, None), // not sure how to hint for arbitrary_loop()
                ]),
            ))
        })
    }

    /// size hint for generate_attr_value_for_schematype()
    #[allow(dead_code)]
    pub fn generate_attr_value_for_schematype_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        arbitrary::size_hint::try_recursion_guard(depth, |depth| {
            Ok(arbitrary::size_hint::or_all(&[
                Self::generate_attr_value_for_type_size_hint(depth)?,
                (1, None), // not sure how to hint for arbitrary_loop()
                Self::arbitrary_uid_with_type_size_hint(depth),
                Self::generate_attr_value_for_type_size_hint(depth)?,
            ]))
        })
    }

    /// generate an arbitrary `Value` of the given `target_type`
    pub fn generate_value_for_type(
        &self,
        target_type: &Type,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Value> {
        use ast::Value;
        match target_type {
            Type::Bool => {
                // the only valid bool-typed attribute value is a bool literal
                let b: bool = u.arbitrary()?;
                Ok(Value::from(b))
            }
            Type::Long => {
                // the only valid long-typed attribute value is an int literal
                Ok(Value::from(self.constant_pool.arbitrary_int_constant(u)?))
            }
            Type::String => {
                // the only valid string-typed attribute value is a string literal
                Ok(Value::from(
                    self.constant_pool.arbitrary_string_constant(u)?,
                ))
            }
            Type::Entity(ety) => {
                // the only valid entity-typed attribute value is a UID literal
                Ok(Value::from(self.arbitrary_uid_with_type(ety, u)?))
            }
            Type::Set(target_element_ty) => {
                // the only valid Set-typed attribute value is a set literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty set
                    Ok(Value::empty_set(None))
                } else {
                    let mut l = Vec::new();
                    u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                        l.push(self.generate_value_for_type(
                            target_element_ty,
                            max_depth - 1,
                            u,
                        )?);
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    Ok(Value::set(l, None))
                }
            }
            Type::Record(m) => {
                // the only valid Record-typed attribute value is a record literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty record
                    Ok(Value::empty_record(None))
                } else {
                    let mut r = IndexMap::new();
                    for (a, qt) in m {
                        if qt.required || u.ratio(1, 2)? {
                            r.insert(
                                a.clone(),
                                self.generate_value_for_type(&qt.ty, max_depth - 1, u)?,
                            );
                        }
                    }
                    Ok(Value::record(r, None))
                }
            }
            _ => Err(Error::ExtensionsDisabled),
        }
    }

    /// get a (fully general) arbitrary constant, as an expression.
    #[allow(dead_code)]
    pub fn generate_const_expr(&self, u: &mut Unstructured<'_>) -> Result<ast::Expr> {
        gen!(u,
        4 => self.generate_literal(u),
        1 => {
            let mut l = Vec::new();
            u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                l.push(self.generate_const_expr(u)?);
                Ok(std::ops::ControlFlow::Continue(()))
            })?;
            Ok(ast::Expr::set(l))
        },
        1 => {
            let mut r = IndexMap::new();
            u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                let attr_name = self.schema.arbitrary_attr(u)?;
                r.insert(attr_name, self.generate_const_expr(u)?);
                Ok(std::ops::ControlFlow::Continue(()))
            })?;
            Ok(ast::Expr::record(r).expect("can't have duplicate keys because `r` was already a HashMap"))
        })
    }

    /// get a literal value or variable of an arbitrary type.
    /// This function is guaranteed to not recurse, directly or indirectly.
    fn generate_literal_or_var(&self, u: &mut Unstructured<'_>) -> Result<ast::Expr> {
        if u.ratio(1, 4)? {
            Ok(ast::Expr::var(u.arbitrary()?))
        } else {
            self.generate_literal(u)
        }
    }

    /// get a literal value of an arbitrary type.
    /// This function is guaranteed to not recurse, directly or indirectly.
    fn generate_literal(&self, u: &mut Unstructured<'_>) -> Result<ast::Expr> {
        gen!(u,
        11 => Ok(ast::Expr::val(u.arbitrary::<bool>()?)),
        10 => Ok(ast::Expr::val(
            self.constant_pool.arbitrary_int_constant(u)?,
        )),
        10 => Ok(ast::Expr::val(
            self.constant_pool.arbitrary_string_constant(u)?,
        )),
        20 => Ok(ast::Expr::val(self.generate_uid(u)?)),
        4 => Ok(ast::Expr::val(u.arbitrary::<ast::EntityUID>()?))
        )
    }

    /// get a UID of a type declared in the schema -- may be a principal,
    /// action, or resource UID. For actions, it will be an action declared in
    /// the schema.
    pub fn generate_uid(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
        uniform!(
            u,
            self.arbitrary_principal_uid(u),
            self.schema.arbitrary_action_uid(u),
            self.arbitrary_resource_uid(u)
        )
    }
    /// size hint for generate_uid()
    #[allow(dead_code)]
    pub fn generate_uid_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_range(0, 2),
            arbitrary::size_hint::or_all(&[
                Self::arbitrary_principal_uid_size_hint(depth),
                Self::arbitrary_action_uid_size_hint(depth),
                Self::arbitrary_resource_uid_size_hint(depth),
            ]),
        )
    }

    /// get a UID of a type that could be used as a `principal` for some action in the schema.
    pub fn arbitrary_principal_uid(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
        self.arbitrary_uid_with_type(
            &self
                .schema
                .arbitrary_principal_type(u)
                .map_err(|e| while_doing("choosing a principal type".into(), e.into()))?,
            u,
        )
    }
    /// size hint for arbitrary_principal_uid()
    pub fn arbitrary_principal_uid_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_choose(None),
            Self::arbitrary_uid_with_type_size_hint(depth),
        )
    }

    /// size hint for arbitrary_action_uid()
    pub fn arbitrary_action_uid_size_hint(_depth: usize) -> (usize, Option<usize>) {
        size_hint_for_choose(None)
    }

    /// get a UID of a type that could be used as a `resource` for some action in the schema.
    pub fn arbitrary_resource_uid(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
        self.arbitrary_uid_with_type(
            &self
                .schema
                .arbitrary_resource_type(u)
                .map_err(|e| while_doing("choosing a resource type".into(), e.into()))?,
            u,
        )
    }
    /// size hint for arbitrary_resource_uid()
    pub fn arbitrary_resource_uid_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_choose(None),
            Self::arbitrary_uid_with_type_size_hint(depth),
        )
    }

    /// generate a UID with the given typename
    pub fn arbitrary_uid_with_type(
        &self,
        ty: &ast::EntityType,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityUID> {
        match self.hierarchy {
            None => generate_uid_with_type(ty.clone(), self.schema.get_uid_enum_choices(ty), u),
            Some(hierarchy) => hierarchy.arbitrary_uid_with_type(Some(self.schema), ty, u),
        }
    }
    /// size hint for arbitrary_uid_with_type()
    pub fn arbitrary_uid_with_type_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::or(
            <ast::Eid as Arbitrary>::size_hint(depth),
            Hierarchy::arbitrary_uid_with_type_size_hint(depth),
        )
    }

    /// Decide if we should fill the current AST node w/ an unknown
    /// We want the chance of generating an unknown to go up the lower in the
    /// AST we are.
    fn should_generate_unknown(&self, max_depth: usize, u: &mut Unstructured<'_>) -> Result<bool> {
        if self.settings.enable_unknowns {
            let chance = self.settings.max_depth - max_depth;
            let choice = u.int_in_range::<usize>(0..=self.settings.max_depth)?;
            Ok(choice <= chance)
        } else {
            Ok(false)
        }
    }
}

/// internal helper function, get a [`abac::Type`] representing a Record
/// with (at least) one attribute of the specified name and type.
fn record_type_with_attr(attr_name: SmolStr, attr_type: Type) -> Type {
    Type::Record(BTreeMap::from_iter([(
        attr_name,
        QualifiedType {
            ty: attr_type,
            required: true,
        },
    )]))
}

#[cfg(test)]
mod faithful_test {
    //! Test module for generating expressions from known byte buffers.
    //! Used to validate that the Lean faithful port produces the same results.

    use super::*;
    use crate::abac::{AvailableExtensionFunctions, ConstantPool, UnknownPool};
    use crate::schema::Schema;
    use crate::settings::ABACSettings;
    use arbitrary::Unstructured;
    use smol_str::SmolStr;

    fn fixed_settings() -> ABACSettings {
        ABACSettings {
            match_types: false,
            max_depth: 2,
            max_width: 3,
            enable_additional_attributes: false,
            enable_like: true,
            enable_action_groups_and_attrs: false,
            enable_arbitrary_func_call: false,
            enable_unknowns: false,
            enable_action_in_constraints: false,
            total_action_request_env_limit: 10,
            max_actions: 5,
        }
    }

    fn fixed_pool() -> ConstantPool {
        ConstantPool::new(
            vec![0, 1, -1, 42, 100],
            vec![
                SmolStr::from("hello"),
                SmolStr::from("world"),
                SmolStr::from("test"),
            ],
        )
    }

    /// Create a Schema from a cedar schema string with a fixed pool.
    fn fixed_schema() -> Schema {
        use cedar_policy_core::validator::json_schema;

        // Use JSON schema format which has stable parsing
        let schema_json = serde_json::json!({
            "": {
                "entityTypes": {
                    "User": {
                        "shape": {
                            "type": "Record",
                            "attributes": {
                                "name": { "type": "String" },
                                "age": { "type": "Long" },
                                "active": { "type": "Boolean" }
                            }
                        }
                    },
                    "Document": {
                        "shape": {
                            "type": "Record",
                            "attributes": {
                                "owner": { "type": "Entity", "name": "User" },
                                "title": { "type": "String" }
                            }
                        }
                    }
                },
                "actions": {
                    "view": {
                        "appliesTo": {
                            "principalTypes": ["User"],
                            "resourceTypes": ["Document"],
                            "context": {
                                "type": "Record",
                                "attributes": {
                                    "reason": { "type": "String" }
                                }
                            }
                        }
                    },
                    "edit": {
                        "appliesTo": {
                            "principalTypes": ["User"],
                            "resourceTypes": ["Document"],
                            "context": { "type": "Record", "attributes": {} }
                        }
                    }
                }
            }
        });

        let frag: json_schema::Fragment<cedar_policy_core::validator::RawName> =
            serde_json::from_value(schema_json).expect("valid json schema");

        let pool_bytes = vec![0u8; 50];
        let mut u = Unstructured::new(&pool_bytes);
        Schema::from_raw_schemafrag(frag, fixed_settings(), &mut u)
            .expect("schema from fragment")
    }

    /// Generate an expression from a byte buffer with the fixed setup.
    /// Returns the expression as a string, or an error description.
    fn gen_expr_from_bytes(expr_bytes: &[u8], max_depth: usize) -> String {
        let schema = fixed_schema();
        let settings = fixed_settings();
        let pool = fixed_pool();
        let ext_funcs = AvailableExtensionFunctions::create(&settings);
        let unknown_pool = UnknownPool::default();

        let mut u = Unstructured::new(expr_bytes);
        let mut gen = ExprGenerator {
            schema: &schema,
            settings: &settings,
            constant_pool: &pool,
            unknown_pool: &unknown_pool,
            ext_funcs: &ext_funcs,
            hierarchy: None,
        };

        match gen.generate_expr(max_depth, &mut u) {
            Ok(expr) => format!("{expr}"),
            Err(e) => format!("ERROR({e:?})"),
        }
    }

    #[test]
    fn print_schema_info() {
        let schema = fixed_schema();
        println!("Entity types: {:?}", schema.entity_types);
        println!("Principal types: {:?}", schema.principal_types);
        println!("Resource types: {:?}", schema.resource_types);
        println!("Actions: {:?}", schema.actions_eids);
        println!("Schema repr: {:?}", schema.schema);
    }

    /// Print test vectors for the Lean side at depth 0 (only literal_or_var).
    /// At depth 0, generate_expr calls generate_literal_or_var directly.
    #[test]
    fn depth0_test_vectors() {
        // depth=0: immediately calls generate_literal_or_var
        // generate_literal_or_var:
        //   ratio(1,4): int_in_range::<u8>(1..=4), true if <= 1
        //   if true → Expr::var(u.arbitrary::<Var>())
        //     Var: int_in_range::<u8>(0..=3)
        //   if false → generate_literal
        //     gen!(u, 11=>bool, 10=>int, 10=>string, 20=>uid, 4=>arbitrary_uid)
        //     total = 55, int_in_range::<u8>(0..=54)

        let test_cases: &[(&str, &[u8])] = &[
            // ratio(1,4): int_in_range(1..=4), delta=3, result=1+(byte%4)
            // true if result<=1, i.e., byte%4==0
            //
            // byte=0: 1+(0%4)=1, 1<=1 → true → var
            // Var: int_in_range(0..=3), delta=3, result=byte%4
            // ratio(1,4): int_in_range::<u8>(1..=4), delta=3, result=1+(byte%4)
            // true if result<=1, i.e., byte%4==0. So byte=0→true, byte=1,2,3→false
            //
            // Var: derived Arbitrary reads u32 (4 bytes), uses Lemire:
            //   index = (u64::from(u32_val) * 4) >> 32
            //   0→Principal, 1→Action, 2→Resource, 3→Context
            //   u32 for Principal: need (val*4)>>32 == 0, i.e., val < 2^30 = 1073741824
            //   u32 for Action: (val*4)>>32 == 1, i.e., val in [1073741824, 2147483648)
            //   u32 for Resource: (val*4)>>32 == 2, i.e., val in [2147483648, 3221225472)
            //   u32 for Context: (val*4)>>32 == 3, i.e., val >= 3221225472
            //
            // u32 bytes are big-endian in int_in_range_impl (first byte is MSB)
            // val = bytes[0]<<24 | bytes[1]<<16 | bytes[2]<<8 | bytes[3]
            //   Actually: it's (arbitrary_int << 8) | byte, built left to right
            //   So first byte is MSB.
            //
            // u32::arbitrary reads 4 bytes LITTLE-ENDIAN via fill_buffer + from_le_bytes
            // Then: index = (u64::from(val) * 4) >> 32
            // For Principal: val < 2^30. LE bytes [0,0,0,0] → val=0 → idx=0
            ("var_principal", &[0, 0, 0, 0, 0]),
            // For Action: need val in [2^30, 2^31). val=0x40000000. LE: [0x00, 0x00, 0x00, 0x40]
            ("var_action", &[0, 0x00, 0x00, 0x00, 0x40]),
            // For Resource: val=0x80000000. LE: [0x00, 0x00, 0x00, 0x80]
            ("var_resource", &[0, 0x00, 0x00, 0x00, 0x80]),
            // For Context: val=0xC0000000. LE: [0x00, 0x00, 0x00, 0xC0]
            ("var_context", &[0, 0x00, 0x00, 0x00, 0xC0]),
            //
            // ratio byte=1: 1+(1%4)=2, 2<=1→false → literal
            // generate_literal: gen!(11,10,10,20,4) total=55
            //   int_in_range(0..=54), delta=54, result=byte%55
            //   byte=0: 0%55=0, 0<11→bool
            //     u.arbitrary::<bool>(): int_in_range(0..=1), byte%2
            ("lit_false", &[1, 0, 0]),   // ratio→false, lit=0→bool, bool=0→false
            ("lit_true", &[1, 0, 1]),    // ratio→false, lit=0→bool, bool=1→true
            //
            // lit byte=11: 11%55=11, 11>=11 → int branch (11<=x<21)
            //   u.choose(&pool.int_constants): choose_index(5)
            //   int_in_range::<usize>(0..=4), delta=4
            //   For usize on 64-bit: reads 1 byte since delta<256
            //   result = byte%5
            ("lit_int_0", &[1, 11, 0]),     // ratio→false, lit=11→int, idx=0%5=0→pool[0]=0
            ("lit_int_42", &[1, 11, 3]),    // ratio→false, lit=11→int, idx=3%5=3→pool[3]=42
            ("lit_int_100", &[1, 11, 4]),   // ratio→false, lit=11→int, idx=4%5=4→pool[4]=100
            //
            // lit byte=21: 21%55=21, 21>=21 → string branch (21<=x<31)
            //   u.choose(&pool.string_constants): choose_index(3)
            //   int_in_range::<usize>(0..=2), delta=2, result=byte%3
            ("lit_str_hello", &[1, 21, 0]), // string idx=0→"hello"
            ("lit_str_world", &[1, 21, 1]), // string idx=1→"world"
            ("lit_str_test", &[1, 21, 2]),  // string idx=2→"test"
        ];

        println!("=== Depth 0 Test Vectors ===");
        println!("Schema: entity type 'a' (enum [\"\"]); action \"action\" {{principal:[a], resource:[a]}}");
        println!("Pool: ints=[0,1,-1,42,100], strings=[\"hello\",\"world\",\"test\"]");
        println!();

        for (name, bytes) in test_cases {
            let result = gen_expr_from_bytes(bytes, 0);
            println!("{name:20} bytes={bytes:?} => {result}");
        }
    }

    /// Replay bytes produced by the Lean faithful generator (with nontrivial schema)
    /// and verify the Rust ExprGenerator produces the same expression.
    #[test]
    fn replay_lean_bytes() {
        let lean_cases: &[(&str, &[u8], &str)] = &[
            // Depth 0 (all padded with 64 zero bytes)
            ("d0_int_1", &[153,184,21,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], "1"),
            ("d0_uid_user", &[51,143,168,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], "User::\"\""),
            ("d0_var_principal", &[172,140,59,21,19,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], "principal"),
            ("d0_str_test", &[45,243,50,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], "\"test\""),
            ("d0_var_action", &[236,90,206,245,70,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], "action"),
            ("d0_var_ctx", &[60,250,51,251,222,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], "context"),
            ("d0_bool_true", &[238,5,225,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], "true"),
            ("d0_str_hello", &[205,243,207,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], "\"hello\""),
        ];

        println!("\n=== Lean→Rust Replay (total=45) ===");
        let mut pass = 0;
        let mut fail = 0;
        for (name, bytes, expected) in lean_cases {
            let result = gen_expr_from_bytes(bytes, if name.starts_with("d1") { 1 } else { 0 });
            let matches = result == *expected;
            if matches {
                pass += 1;
                println!("  PASS {name:20} => {result}");
            } else {
                fail += 1;
                println!("  FAIL {name:20} => {result} (expected: {expected})");
            }
        }
        println!("\n  {pass} passed, {fail} failed");
        assert_eq!(fail, 0, "Some Lean→Rust replays failed");
    }

    /// Test that String::arbitrary with zero-padded buffer produces ""
    #[test]
    fn test_uid_string_arbitrary_with_padding() {
        // ratio=1 (false → literal), gen=31 (UID branch, 31<51), uniform=0 (principal)
        // Then: principal_type → User (0 bytes), generate_uid_with_type(User) → Eid::arbitrary
        // With padding zeros, String::arbitrary reads tail → size=0 → ""
        let mut bytes: Vec<u8> = vec![1, 31, 0];
        bytes.extend(vec![0u8; 64]);
        let result = gen_expr_from_bytes(&bytes, 0);
        println!("principal uid: {result}");
        assert_eq!(result, "User::\"\"");

        // uniform=1 → action uid (choose from 2 actions, 1 byte)
        let mut bytes2: Vec<u8> = vec![1, 31, 1, 0]; // extra byte for choose_index(2)
        bytes2.extend(vec![0u8; 64]);
        let result2 = gen_expr_from_bytes(&bytes2, 0);
        println!("action uid: {result2}");
        assert_eq!(result2, "Action::\"edit\"");

        // uniform=2 → resource uid → Document::""
        let mut bytes3: Vec<u8> = vec![1, 31, 2];
        bytes3.extend(vec![0u8; 64]);
        let result3 = gen_expr_from_bytes(&bytes3, 0);
        println!("resource uid: {result3}");
        assert_eq!(result3, "Document::\"\"");
    }

    /// More depth-1 vectors including UIDs and getAttr
    #[test]
    fn replay_lean_depth1_extended() {
        let lean_cases: &[(&str, &[u8], &str)] = &[
            // !Document::""
            ("d1_not_doc", &[218,249,49,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "!Document::\"\""),
            // Document::"".owner (getAttr)
            ("d1_getattr_owner", &[169,75,179,135,214,151,224,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "Document::\"\".owner"),
            // "test" == User::""
            ("d1_eq_test_user", &[7,125,137,98,154,215,219,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "\"test\" == User::\"\""),
            // !User::""
            ("d1_not_user", &[153,150,157,180,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "!User::\"\""),
        ];

        println!("\n=== Lean→Rust Depth 1 Extended ===");
        let mut pass = 0;
        let mut fail = 0;
        for (name, bytes, expected) in lean_cases {
            let result = gen_expr_from_bytes(bytes, 1);
            let matches = result == *expected;
            if matches { pass += 1; println!("  PASS {name:20} => {result}"); }
            else { fail += 1; println!("  FAIL {name:20} => {result} (expected: {expected})"); }
        }
        println!("\n  {pass} passed, {fail} failed");
        assert_eq!(fail, 0, "Some depth-1 extended replays failed");
    }

    /// Test set/record/hasTag branches
    #[test]
    fn replay_lean_set_record() {
        let lean_cases: &[(&str, &[u8], &str)] = &[
            // All constructed with: outer byte % 5 = 4 → inner gen
            // Sub-expr "false" = [1, 0, 0] (ratio=1→literal, gen=0→bool, bool=0→false)
            // Sub-expr "principal" = [0, 0, 0, 0, 0] (ratio=0→var, u32=0→Principal)

            // record empty: inner=28(record), count byte=0(%4=0)
            ("d1_record_empty", &[4, 28, 0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "{}"),
            // set empty: inner=27(set), count byte=0(%4=0)
            ("d1_set_empty", &[4, 27, 0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "[]"),
            // set with 1 element (false): inner=27(set), count byte=1(%4=1), sub=[1,0,0]
            ("d1_set_one", &[4, 27, 1, 1, 0, 0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "[false]"),
            // in/mem: inner=14(14<20→mem), sub1=false[1,0,0], sub2=false[1,0,0]
            ("d1_in", &[4, 14, 1, 0, 0, 1, 0, 0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "false in false"),
            // isEmpty: inner=23, sub=false[1,0,0]
            ("d1_isempty", &[4, 23, 1, 0, 0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "false.isEmpty()"),
            // is: inner=26, sub-expr first then entity_type
            //   sub=principal[0,0,0,0,0] (5 bytes), then choose_index(2)=byte→entity_types[idx]
            ("d1_is", &[4, 26, 0, 0, 0, 0, 0, 0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "principal is Document"),
            // neg: inner=13, sub=false[1,0,0]
            ("d1_neg", &[4, 13, 1, 0, 0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "-(false)"),
            // add: inner=10, sub1=false[1,0,0], sub2=false[1,0,0]
            ("d1_add", &[4, 10, 1, 0, 0, 1, 0, 0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "false + false"),
            // getAttr: inner=30, attr chosen first then sub-expr
            //   gen!(1=>arb_str, 6=>schema_attr): byte=1(%7=1, >=1→schema_attr)
            //   choose_index(numAttrs): byte=3→attrs[3] (Rust says "age")
            //   then sub-expr false=[1,0,0]
            ("d1_getattr", &[4, 30, 1, 3, 1, 0, 0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "false.age"),
            // hasAttr: inner=37, uniform!(schema_attr, arb_str)
            //   byte=0(%2=0→schema_attr), choose_index byte=0→attrs[0] (Rust says "owner")
            //   then sub-expr false=[1,0,0]
            ("d1_hasattr", &[4, 37, 0, 0, 1, 0, 0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "false has owner"),
            // hasTag: inner=41, uniform!(generate_expr, val(schema_attr))
            //   byte=1(%2=1→val(schema_attr)), choose_index byte=0→attrs[0]="owner"
            //   then sub-expr false=[1,0,0]
            ("d1_hastag", &[4, 41, 1, 0, 1, 0, 0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "false.hasTag(\"owner\")"),
            // Lean-generated: true.name (getAttr with correct 5-attr index)
            ("d1_lean_getattr_name", &[84,31,214,144,246,166,181,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
             "true.name"),
        ];

        println!("\n=== Set/Record/Branch Tests ===");
        let mut pass = 0;
        let mut fail = 0;
        for (name, bytes, expected) in lean_cases {
            let result = gen_expr_from_bytes(bytes, 1);
            let matches = result == *expected;
            if matches { pass += 1; println!("  PASS {name:25} => {result}"); }
            else { fail += 1; println!("  FAIL {name:25} => {result} (expected: {expected})"); }
        }
        println!("\n  {pass} passed, {fail} failed");
        assert_eq!(fail, 0, "Set/record replays failed");
    }

    /// Debug a specific failing buffer - trace what Rust sees
    #[test]
    fn debug_remaining_trace() {
        // Failing case: depth=6, 268 bytes
        // Lean: (if (User::"" == bEdNt0l26eq::...::J1R2UrJtAI::"") then ... else ...)
        // Rust: (if (User::"" == bEdNt0l26eq::...::J1R2UrJtAI::"") then ... else ...) -- DIFFERENT sub-expr
        let buf: &[u8] = &[12, 59, 225, 172, 40, 101, 206, 147, 141, 34, 218, 107, 52, 133, 68, 160, 111, 168, 64, 216, 65, 30, 179, 145, 55, 136, 144, 61, 133, 140, 39, 86, 244, 0, 47, 128, 132, 103, 178, 9, 173, 136, 158, 229, 16, 241, 2, 27, 60, 140, 200, 170, 105, 127, 163, 100, 226, 229, 144, 44, 199, 123, 218, 226, 123, 243, 80, 235, 34, 32, 247, 182, 186, 101, 65, 134, 95, 140, 27, 11, 111, 110, 178, 82, 33, 226, 237, 41, 183, 66, 90, 102, 218, 80, 123, 206, 233, 219, 254, 14, 241, 89, 163, 77, 207, 209, 167, 110, 57, 130, 122, 234, 20, 34, 144, 101, 29, 58, 89, 218, 33, 65, 160, 204, 19, 13, 26, 57, 175, 37, 73, 94, 188, 28, 199, 131, 246, 75, 44, 27, 84, 237, 7, 112, 48, 28, 197, 152, 39, 182, 114, 221, 209, 43, 37, 112, 236, 186, 125, 155, 162, 54, 219, 134, 92, 205, 246, 71, 16, 76, 38, 150, 46, 138, 35, 49, 121, 66, 197, 118, 179, 175, 214, 8, 68, 43, 222, 167, 229, 32, 41, 64, 94, 3, 161, 114, 247, 223, 129, 158, 184, 166, 82, 180, 233, 86, 106, 250, 144, 143, 14, 28, 179, 206, 160, 43, 158, 200, 224, 157, 21, 56, 29, 154, 134, 237, 80, 199, 253, 188, 184, 186, 5, 167, 223, 120, 211, 29, 45, 143, 174, 12, 86, 205, 13, 93, 76, 70, 81, 12, 103, 134, 229, 181, 192, 206, 81, 113, 28, 66, 67, 215, 175, 175, 1, 0, 0, 0];

        println!("=== Buffer Analysis ===");
        println!("Total: {} bytes", buf.len());
        println!("Last 10: {:?}", &buf[buf.len()-10..]);
        // Lean says there are 4 tail entries (last 4 bytes: [1, 0, 0, 0])
        // Tail entries reversed at end. Last byte = entry[0], second-to-last = entry[1], etc.
        println!("Tail bytes (last 4): {:?}", &buf[buf.len()-4..]);
        println!();

        // What does Rust produce?
        let result = gen_expr_from_bytes(buf, 6);
        println!("Rust result: {result}");
        println!();

        // Now trace String::arbitrary calls
        // Let's manually simulate what generate_expr does with this buffer
        // by calling String::arbitrary at various points
        println!("=== String::arbitrary at decreasing remaining ===");
        for consumed_from_front in (0..buf.len()).step_by(20) {
            if consumed_from_front >= buf.len() { break; }
            let sub_buf = &buf[consumed_from_front..];
            let mut u = Unstructured::new(sub_buf);
            let remaining_before = u.len();
            match <String as Arbitrary>::arbitrary(&mut u) {
                Ok(s) => println!("  front_consumed={consumed_from_front} remaining={remaining_before}: String={:?} (len={}) remaining_after={}", s, s.len(), u.len()),
                Err(e) => println!("  front_consumed={consumed_from_front} remaining={remaining_before}: ERROR {e:?}"),
            }
        }
    }
}
