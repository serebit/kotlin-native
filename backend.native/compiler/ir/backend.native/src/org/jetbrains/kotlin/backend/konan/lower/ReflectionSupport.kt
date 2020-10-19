/*
 * Copyright 2010-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the LICENSE file.
 */

package org.jetbrains.kotlin.backend.konan.lower

import org.jetbrains.kotlin.backend.konan.InteropFqNames
import org.jetbrains.kotlin.backend.konan.KonanBackendContext
import org.jetbrains.kotlin.backend.konan.ir.typeWithStarProjections
import org.jetbrains.kotlin.backend.konan.ir.typeWithoutArguments
import org.jetbrains.kotlin.backend.konan.isObjCClass
import org.jetbrains.kotlin.backend.konan.llvm.fullName
import org.jetbrains.kotlin.backend.konan.reportCompilationError
import org.jetbrains.kotlin.descriptors.ClassDescriptor
import org.jetbrains.kotlin.ir.IrElement
import org.jetbrains.kotlin.ir.builders.*
import org.jetbrains.kotlin.ir.declarations.IrEnumEntry
import org.jetbrains.kotlin.ir.declarations.IrFile
import org.jetbrains.kotlin.ir.declarations.IrFunction
import org.jetbrains.kotlin.ir.declarations.IrTypeParameter
import org.jetbrains.kotlin.ir.expressions.IrExpression
import org.jetbrains.kotlin.ir.expressions.IrMemberAccessExpression
import org.jetbrains.kotlin.ir.expressions.impl.IrGetEnumValueImpl
import org.jetbrains.kotlin.ir.expressions.impl.IrVarargImpl
import org.jetbrains.kotlin.ir.symbols.IrClassSymbol
import org.jetbrains.kotlin.ir.symbols.IrTypeParameterSymbol
import org.jetbrains.kotlin.ir.types.*
import org.jetbrains.kotlin.ir.util.*
import org.jetbrains.kotlin.ir.util.irCall
import org.jetbrains.kotlin.resolve.descriptorUtil.fqNameUnsafe
import org.jetbrains.kotlin.resolve.descriptorUtil.getAllSuperClassifiers
import org.jetbrains.kotlin.types.Variance

internal class KTypeGenerator(val context: KonanBackendContext, val irFile: IrFile, val irElement: IrElement) {
    private val symbols = context.ir.symbols

    fun IrBuilderWithScope.irKType(type: IrType,
                                   needExactTypeParameters: Boolean = false,
                                   leaveReifiedForLater: Boolean = false
    ) = irKType(type, BuildingContext(needExactTypeParameters, leaveReifiedForLater, mutableSetOf()))

    private class BuildingContext(val needExactTypeParameters: Boolean, var leaveReifiedForLater: Boolean,
                                  val seenTypeParameters: MutableSet<IrTypeParameter>)

    private class RecursiveBoundsException(message: String) : Throwable(message)

    private fun IrBuilderWithScope.irKType(type: IrType, context: BuildingContext): IrExpression {
        if (type !is IrSimpleType) {
            // Represent as non-denotable type:
            return irKTypeImpl(
                    kClassifier = irNull(),
                    irTypeArguments = emptyList(),
                    isMarkedNullable = false,
                    context = context
            )
        }
        try {
            val kClassifier = when (val classifier = type.classifier) {
                is IrClassSymbol -> irKClass(classifier)
                is IrTypeParameterSymbol -> {
                    if (classifier.owner.isReified && context.leaveReifiedForLater) {
                        // Leave as is for reification.
                        return irCall(symbols.typeOf).apply { putTypeArgument(0, type) }
                    }

                    context.leaveReifiedForLater = false
                    irKTypeParameter(classifier.owner, context)
                }
                else -> TODO("Unexpected classifier: $classifier")
            }

            return irKTypeImpl(
                    kClassifier = kClassifier,
                    irTypeArguments = type.arguments,
                    isMarkedNullable = type.hasQuestionMark,
                    context = context
            )
        } catch (t: RecursiveBoundsException) {
            if (context.needExactTypeParameters)
                this@KTypeGenerator.context.reportCompilationError(t.message!!, irFile, irElement)
            return irCall(symbols.kTypeImplForTypeParametersWithRecursiveBounds.constructors.single())
        }
    }

    private fun IrBuilderWithScope.irKTypeImpl(
            kClassifier: IrExpression,
            irTypeArguments: List<IrTypeArgument>,
            isMarkedNullable: Boolean,
            context: BuildingContext
    ): IrExpression = irCall(symbols.kTypeImpl.constructors.single()).apply {
        putValueArgument(0, kClassifier)
        putValueArgument(1, irKTypeProjectionsList(irTypeArguments, context))
        putValueArgument(2, irBoolean(isMarkedNullable))
    }

    private fun IrBuilderWithScope.irKClass(symbol: IrClassSymbol) = irKClass(this@KTypeGenerator.context, symbol)

    private fun IrBuilderWithScope.irKTypeParameter(typeParameter: IrTypeParameter, context: BuildingContext): IrMemberAccessExpression<*> {
        if (!context.seenTypeParameters.add(typeParameter))
            throw RecursiveBoundsException("Non-reified type parameters with recursive bounds are not supported yet: ${typeParameter.render()}")
        val result = irCall(symbols.kTypeParameterImpl.constructors.single()).apply {
            putValueArgument(0, irString(typeParameter.name.asString()))
            putValueArgument(1, irString(typeParameter.parentUniqueName))
            putValueArgument(2, irKTypeList(typeParameter.superTypes, context))
            putValueArgument(3, irKVariance(typeParameter.variance))
            putValueArgument(4, irBoolean(typeParameter.isReified))
        }
        context.seenTypeParameters.remove(typeParameter)
        return result
    }

    private val IrTypeParameter.parentUniqueName get() = when (val parent = parent) {
        is IrFunction -> parent.fullName
        else -> parent.fqNameForIrSerialization.asString()
    }

    private fun IrBuilderWithScope.irKVariance(variance: Variance) =
            IrGetEnumValueImpl(
                    startOffset, endOffset,
                    symbols.kVariance.defaultType,
                    symbols.kVariance.owner.declarations.filterIsInstance<IrEnumEntry>()[variance.ordinal].symbol
            )

    private fun <T> IrBuilderWithScope.irKTypeLikeList(
            types: List<T>,
            itemType: IrType,
            itemBuilder: (T) -> IrExpression
    ) = if (types.isEmpty()) {
        irCall(symbols.emptyList, listOf(itemType))
    } else {
        irCall(symbols.listOf, listOf(itemType)).apply {
            putValueArgument(0, IrVarargImpl(
                    startOffset, endOffset,
                    type = symbols.array.typeWith(itemType),
                    varargElementType = itemType,
                    elements = types.map { itemBuilder(it) }
            ))
        }
    }

    private fun IrBuilderWithScope.irKTypeList(types: List<IrType>, context: BuildingContext) =
            irKTypeLikeList(types, symbols.kType.defaultType) { irKType(it, context) }

    private fun IrBuilderWithScope.irKTypeProjectionsList(irTypeArguments: List<IrTypeArgument>, context: BuildingContext) =
            irKTypeLikeList(irTypeArguments, symbols.kTypeProjection.typeWithoutArguments) {
                irKTypeProjection(it, context)
            }

    private fun IrBuilderWithScope.irKTypeProjection(argument: IrTypeArgument, context: BuildingContext) =
            when (argument) {
                is IrTypeProjection -> irCall(symbols.kTypeProjectionFactories.getValue(argument.variance)).apply {
                    dispatchReceiver = irGetObject(symbols.kTypeProjectionCompanion)
                    putValueArgument(0, irKType(argument.type, context))
                }

                is IrStarProjection -> irCall(symbols.kTypeProjectionStar.owner.getter!!).apply {
                    dispatchReceiver = irGetObject(symbols.kTypeProjectionCompanion)
                }

                else -> error("Unexpected IrTypeArgument: $argument (${argument::class})")
            }
}

internal fun IrBuilderWithScope.irKClass(context: KonanBackendContext, symbol: IrClassSymbol): IrExpression {
    val symbols = context.ir.symbols
    return when {
        symbol.descriptor.isObjCClass() ->
            irKClassUnsupported(context, "KClass for Objective-C classes is not supported yet")

        symbol.descriptor.getAllSuperClassifiers().any {
            it is ClassDescriptor && it.fqNameUnsafe == InteropFqNames.nativePointed
        } -> irKClassUnsupported(context, "KClass for interop types is not supported yet")

        else -> irCall(symbols.kClassImplConstructor.owner).apply {
            putValueArgument(0, irCall(symbols.getClassTypeInfo, listOf(symbol.typeWithStarProjections)))
        }
    }
}

private fun IrBuilderWithScope.irKClassUnsupported(context: KonanBackendContext, message: String) =
        irCall(context.ir.symbols.kClassUnsupportedImplConstructor.owner).apply {
            putValueArgument(0, irString(message))
        }
