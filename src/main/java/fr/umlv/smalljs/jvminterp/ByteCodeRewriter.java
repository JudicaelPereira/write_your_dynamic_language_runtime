package fr.umlv.smalljs.jvminterp;

import static java.lang.invoke.MethodType.genericMethodType;
import static java.nio.charset.StandardCharsets.UTF_8;
import static org.objectweb.asm.Opcodes.*;

import java.io.PrintWriter;
import java.lang.invoke.CallSite;
import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodHandles.Lookup;
import java.lang.invoke.MethodType;
import java.util.List;
import java.util.Map;

import fr.umlv.smalljs.rt.Failure;
import org.objectweb.asm.*;
import org.objectweb.asm.util.CheckClassAdapter;

import fr.umlv.smalljs.ast.Expr;
import fr.umlv.smalljs.ast.Expr.Block;
import fr.umlv.smalljs.ast.Expr.Call;
import fr.umlv.smalljs.ast.Expr.FieldAccess;
import fr.umlv.smalljs.ast.Expr.FieldAssignment;
import fr.umlv.smalljs.ast.Expr.Fun;
import fr.umlv.smalljs.ast.Expr.Identifier;
import fr.umlv.smalljs.ast.Expr.If;
import fr.umlv.smalljs.ast.Expr.Literal;
import fr.umlv.smalljs.ast.Expr.MethodCall;
import fr.umlv.smalljs.ast.Expr.ObjectLiteral;
import fr.umlv.smalljs.ast.Expr.Return;
import fr.umlv.smalljs.ast.Expr.VarAssignment;
import fr.umlv.smalljs.rt.JSObject;

public final class ByteCodeRewriter {
    static JSObject createFunction(String name, List<String> parameters, Block body, JSObject global) {
        var env = JSObject.newEnv(null);

        env.register("this", 0);
        for (String parameter : parameters) {
            env.register(parameter, env.length());
        }
        var parameterCount = env.length();
        visitVariable(body, env);
        var localVariableCount = env.length();

        var cv = new ClassWriter(ClassWriter.COMPUTE_MAXS | ClassWriter.COMPUTE_FRAMES);
        cv.visit(V25, ACC_PUBLIC | ACC_SUPER, "script", null, "java/lang/Object", null);
        cv.visitSource("script", null);

        var methodType = genericMethodType(1 + parameters.size());
        var desc = methodType.toMethodDescriptorString();
        var mv = cv.visitMethod(ACC_PUBLIC | ACC_STATIC, name, desc, null, null);
        mv.visitCode();

        //initialize local variables to undefined by default
        for(var i = parameterCount; i < localVariableCount; i++) {
            mv.visitLdcInsn(new ConstantDynamic("undefined", "Ljava/lang/Object;", BSM_UNDEFINED));
            mv.visitVarInsn(ASTORE, i);
        }

        var dictionary = new FunDictionary();
        visit(body, env, mv, dictionary);

        mv.visitLdcInsn(new ConstantDynamic("undefined", "Ljava/lang/Object;", BSM_UNDEFINED));
        mv.visitInsn(ARETURN);
        mv.visitMaxs(0, 0);
        mv.visitEnd();

        var instrs = cv.toByteArray();
        dumpBytecode(instrs);

        var functionClassLoader = new FunClassLoader(dictionary, global);
        var type = functionClassLoader.createClass("script", instrs);

        MethodHandle mh;
        try {
            mh = MethodHandles.lookup().findStatic(type, name, methodType);
        } catch (NoSuchMethodException | IllegalAccessException e) {
            throw new AssertionError(e);
        }

        return JSObject.newFunction(name, mh);
    }

    private static void dumpBytecode(byte[] array) {
        var reader = new ClassReader(array);
        CheckClassAdapter.verify(reader, true, new PrintWriter(System.err, false, UTF_8));
    }

    private static void visitVariable(Expr expression, JSObject env) {
        switch (expression) {
            case Block(List<Expr> exprs, _) -> {
                for (var expr : exprs) {
                    visitVariable(expr, env);
                }
            }
            case VarAssignment(String name, _, boolean declaration, _) -> {
                if (declaration) {
                    env.register(name, env.length());
                }
            }
            case If(_, Block trueBlock, Block falseBlock, _) -> {
                visitVariable(trueBlock, env);
                visitVariable(falseBlock, env);
            }
            case Literal _, Call _, Identifier _, Fun _, Return _, ObjectLiteral _, FieldAccess _,
                 FieldAssignment _, MethodCall _ -> {
                // do nothing
            }
        };
    }

    private static Handle bsm(String name, Class<?> returnType, Class<?>... parameterTypes) {
        return new Handle(H_INVOKESTATIC,
                RT_NAME, name,
                MethodType.methodType(returnType, parameterTypes).toMethodDescriptorString(), false);
    }

    private static final String JSOBJECT = JSObject.class.getName().replace('.', '/');
    private static final String RT_NAME = RT.class.getName().replace('.', '/');
    private static final Handle BSM_UNDEFINED = bsm("bsm_undefined", Object.class, Lookup.class, String.class, Class.class);
    private static final Handle BSM_CONST = bsm("bsm_const", Object.class, Lookup.class, String.class, Class.class, int.class);
    private static final Handle BSM_FUNCALL = bsm("bsm_funcall", CallSite.class, Lookup.class, String.class, MethodType.class);
    private static final Handle BSM_GLOBALCALL = bsm("bsm_globalcall", CallSite.class, Lookup.class, String.class, MethodType.class, String.class);
    private static final Handle BSM_LOOKUP = bsm("bsm_lookup", CallSite.class, Lookup.class, String.class, MethodType.class, String.class);
    private static final Handle BSM_FUN = bsm("bsm_fun", Object.class, Lookup.class, String.class, Class.class, int.class);
    private static final Handle BSM_REGISTER = bsm("bsm_register", CallSite.class, Lookup.class, String.class, MethodType.class, String.class);
    private static final Handle BSM_TRUTH = bsm("bsm_truth", CallSite.class, Lookup.class, String.class, MethodType.class);
    private static final Handle BSM_GET = bsm("bsm_get", CallSite.class, Lookup.class, String.class, MethodType.class, String.class);
    private static final Handle BSM_SET = bsm("bsm_set", CallSite.class, Lookup.class, String.class, MethodType.class, String.class);
    private static final Handle BSM_METHODCALL = bsm("bsm_methodcall", CallSite.class, Lookup.class, String.class, MethodType.class);

    private static void visit(Expr expression, JSObject env, MethodVisitor mv, FunDictionary dictionary) {
        switch(expression) {
            case Block(List<Expr> exprs, int lineNumber) -> {
                // for each expression
                for (var expr : exprs) {
                    // generate line numbers
                    var label = new Label();
                    mv.visitLabel(label);
                    mv.visitLineNumber(lineNumber, label);
                    // visit it
                    visit(expr, env, mv, dictionary);
                    // if not a statement, generate a POP
                    if (!(expr instanceof Expr.Statement)) {
                        mv.visitInsn(POP);
                    }
                }
            }
            case Literal(Integer integer, int lineNumber) -> {
                // use visitLDCInstr with a ConstantDynamic because the JVM does not support Integer (but supports int)
                mv.visitLdcInsn(new ConstantDynamic("integer", "Ljava/lang/Object;", BSM_CONST, integer));
            }
            case Literal(String s, int lineNumber) -> {
                // use visitLDCInstr because the JVM natively supports string
                mv.visitLdcInsn(s);
            }
            case Literal _ -> {  // should be UNDEFINED
                // use visitLDCInstr with a ConstantDynamic because the JVM does not support UNDEFINED natively
                mv.visitLdcInsn(new ConstantDynamic("undefined", "Ljava/lang/Object;", BSM_UNDEFINED));
            }
            case Call(Expr qualifier, List<Expr> args, int lineNumber) -> {
                // visit the qualifier
                visit(qualifier, env, mv, dictionary);
                // load "this"
                mv.visitLdcInsn(new ConstantDynamic("undefined", "Ljava/lang/Object;", BSM_UNDEFINED));
                // for each argument, visit it
                for (var arg : args) {
                    visit(arg, env, mv, dictionary);
                }
                // generate an invokedynamic
                var desc = "(" + "Ljava/lang/Object;".repeat(2 + args.size()) + ")" + "Ljava/lang/Object;";
                mv.visitInvokeDynamicInsn("funcall", desc, BSM_FUNCALL);
            }
            case VarAssignment(String name, Expr expr, boolean declaration, int lineNumber) -> {
                // visit the expression
                visit(expr, env, mv, dictionary);
                // lookup that name in the environment
                var slot = env.lookupOrDefault(name, null);
                // if it does not exist throw a Failure
                if (slot == null) {
                    throw new Failure("undefined variable");
                }
                // otherwise STORE the top of the stack at the local variable slot
                mv.visitVarInsn(ASTORE, (int) slot);
            }
            case Identifier(String name, int lineNumber) -> {
                // lookup to find if it's a local var access or a lookup access
                var slot = env.lookupOrDefault(name, null);
                // if it does not exist
                if (slot == null) {
                    //  generate an invokedynamic doing a lookup
                    mv.visitInvokeDynamicInsn("lookup", "()Ljava/lang/Object;", BSM_LOOKUP, name);
                } else { // otherwise
                    //  load the local variable at the slot
                    mv.visitVarInsn(ALOAD, (int) slot);
                }
            }
            case Fun fun -> {
                var name = fun.name();
                var toplevel = fun.toplevel();
                // register the fun inside the fun dictionary and get the corresponding id
                var funID = dictionary.register(fun);
                // emit a LDC to load the function corresponding to the id at runtime
                mv.visitLdcInsn(new ConstantDynamic(name, "Ljava/lang/Object;", BSM_FUN, funID));
                // generate an invokedynamic doing a register with the function name if it's a toplevel
                if (toplevel) {
                    mv.visitInsn(DUP);
                    mv.visitInvokeDynamicInsn("register", "(Ljava/lang/Object;)V", BSM_REGISTER, name);
                }
            }
            case Return(Expr expr, int lineNumber) -> {
                // visit the return expression
                visit(expr, env, mv, dictionary);
                // generate the bytecode
                mv.visitInsn(ARETURN);
            }
            case If(Expr condition, Block trueBlock, Block falseBlock, int lineNumber) -> {
                throw new UnsupportedOperationException("TODO If");
                // visit the condition
                // generate an invokedynamic to transform an Object to a boolean using BSM_TRUTH
                // visit the true block
                // visit the false block
            }
            case ObjectLiteral(Map<String, Expr> initMap, int lineNumber) -> {
                throw new UnsupportedOperationException("TODO ObjectLiteral");
                // call newObject with an INVOKESTATIC
                // for each initialization expression
                // generate a string with the key
                // call register on the JSObject
            }
            case FieldAccess(Expr receiver, String name, int lineNumber) -> {
                throw new UnsupportedOperationException("TODO FieldAccess");
                // visit the receiver
                // generate an invokedynamic that goes a get through BSM_GET
            }
            case FieldAssignment(Expr receiver, String name, Expr expr, int lineNumber) -> {
                throw new UnsupportedOperationException("TODO FieldAssignment");
                // visit the receiver
                // visit the expression
                // generate an invokedynamic that goes a set through BSM_SET
            }
            case MethodCall(Expr receiver, String name, List<Expr> args, int lineNumber) -> {
                throw new UnsupportedOperationException("TODO MethodCall");
                // visit the receiver
                // for each argument
                // visit the argument
                // generate an invokedynamic that call BSM_METHODCALL
            }
        }
    }
}
