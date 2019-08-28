/*
 * Copyright (C) 2011 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.android.cglib.dx;

import static java.lang.reflect.Modifier.PRIVATE;
import static java.lang.reflect.Modifier.STATIC;
import static com.android.cglib.dx.rop.code.AccessFlags.ACC_CONSTRUCTOR;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;

import com.android.cglib.dx.dex.DexFormat;
import com.android.cglib.dx.dex.DexOptions;
import com.android.cglib.dx.dex.code.DalvCode;
import com.android.cglib.dx.dex.code.PositionList;
import com.android.cglib.dx.dex.code.RopTranslator;
import com.android.cglib.dx.dex.file.ClassDefItem;
import com.android.cglib.dx.dex.file.DexFile;
import com.android.cglib.dx.dex.file.EncodedField;
import com.android.cglib.dx.dex.file.EncodedMethod;
import com.android.cglib.dx.rop.code.AccessFlags;
import com.android.cglib.dx.rop.code.LocalVariableInfo;
import com.android.cglib.dx.rop.code.RopMethod;
import com.android.cglib.dx.rop.cst.CstString;
import com.android.cglib.dx.rop.cst.CstType;
import com.android.cglib.dx.rop.type.StdTypeList;


public final class DexMaker {
    private final Map<TypeId<?>, TypeDeclaration> types
            = new LinkedHashMap<TypeId<?>, TypeDeclaration>();

    /**
     * Creates a new {@code DexMaker} instance, which can be used to create a
     * single dex file.
     */
    public DexMaker() {
    }

    private TypeDeclaration getTypeDeclaration(TypeId<?> type) {
        TypeDeclaration result = types.get(type);
        if (result == null) {
            result = new TypeDeclaration(type);
            types.put(type, result);
        }
        return result;
    }

    /**
     * Declares {@code type}.
     *
     * @param flags a bitwise combination of {@link Modifier#PUBLIC}, {@link
     *     Modifier#FINAL} and {@link Modifier#ABSTRACT}.
     */
    public void declare(TypeId<?> type, String sourceFile, int flags,
            TypeId<?> supertype, TypeId<?>... interfaces) {
        TypeDeclaration declaration = getTypeDeclaration(type);
        int supportedFlags = Modifier.PUBLIC | Modifier.FINAL | Modifier.ABSTRACT;
        if ((flags & ~supportedFlags) != 0) {
            throw new IllegalArgumentException("Unexpected flag: "
                    + Integer.toHexString(flags));
        }
        if (declaration.declared) {
            throw new IllegalStateException("already declared: " + type);
        }
        declaration.declared = true;
        declaration.flags = flags;
        declaration.supertype = supertype;
        declaration.sourceFile = sourceFile;
        declaration.interfaces = new TypeList(interfaces);
    }

    /**
     * Declares a method or constructor.
     *
     * @param flags a bitwise combination of {@link Modifier#PUBLIC}, {@link
     *     Modifier#PRIVATE}, {@link Modifier#PROTECTED}, {@link Modifier#STATIC},
     *     {@link Modifier#FINAL} and {@link Modifier#SYNCHRONIZED}.
     *     <p><strong>Warning:</strong> the {@link Modifier#SYNCHRONIZED} flag
     *     is insufficient to generate a synchronized method. You must also use
     *     {@link Code#monitorEnter} and {@link Code#monitorExit} to acquire
     *     a monitor.
     */
    public Code declare(MethodId<?, ?> method, int flags) {
        TypeDeclaration typeDeclaration = getTypeDeclaration(method.declaringType);
        if (typeDeclaration.methods.containsKey(method)) {
            throw new IllegalStateException("already declared: " + method);
        }

        int supportedFlags = Modifier.PUBLIC | Modifier.PRIVATE | Modifier.PROTECTED
                | Modifier.STATIC | Modifier.FINAL | Modifier.SYNCHRONIZED;
        if ((flags & ~supportedFlags) != 0) {
            throw new IllegalArgumentException("Unexpected flag: "
                    + Integer.toHexString(flags));
        }

        // replace the SYNCHRONIZED flag with the DECLARED_SYNCHRONIZED flag
        if ((flags & Modifier.SYNCHRONIZED) != 0) {
            flags = (flags & ~Modifier.SYNCHRONIZED) | AccessFlags.ACC_DECLARED_SYNCHRONIZED;
        }

        if (method.isConstructor()) {
            flags |= ACC_CONSTRUCTOR;
        }

        MethodDeclaration methodDeclaration = new MethodDeclaration(method, flags);
        typeDeclaration.methods.put(method, methodDeclaration);
        return methodDeclaration.code;
    }

    /**
     * Declares a field.
     *
     * @param flags a bitwise combination of {@link Modifier#PUBLIC}, {@link
     *     Modifier#PRIVATE}, {@link Modifier#PROTECTED}, {@link Modifier#STATIC},
     *     {@link Modifier#FINAL}, {@link Modifier#VOLATILE}, and {@link
     *     Modifier#TRANSIENT}.
     * @param staticValue a constant representing the initial value for the
     *     static field, possibly null. This must be null if this field is
     *     non-static.
     */
    public void declare(FieldId<?, ?> fieldId, int flags, Object staticValue) {
        TypeDeclaration typeDeclaration = getTypeDeclaration(fieldId.declaringType);
        if (typeDeclaration.fields.containsKey(fieldId)) {
            throw new IllegalStateException("already declared: " + fieldId);
        }

        int supportedFlags = Modifier.PUBLIC | Modifier.PRIVATE | Modifier.PROTECTED
                | Modifier.STATIC | Modifier.FINAL | Modifier.VOLATILE | Modifier.TRANSIENT;
        if ((flags & ~supportedFlags) != 0) {
            throw new IllegalArgumentException("Unexpected flag: "
                    + Integer.toHexString(flags));
        }

        if ((flags & Modifier.STATIC) == 0 && staticValue != null) {
            throw new IllegalArgumentException("staticValue is non-null, but field is not static");
        }

        FieldDeclaration fieldDeclaration = new FieldDeclaration(fieldId, flags, staticValue);
        typeDeclaration.fields.put(fieldId, fieldDeclaration);
    }

    /**
     * Generates a dex file and returns its bytes.
     */
    public byte[] generate() {
        DexOptions options = new DexOptions();
        options.targetApiLevel = DexFormat.API_NO_EXTENDED_OPCODES;
        DexFile outputDex = new DexFile(options);

        for (TypeDeclaration typeDeclaration : types.values()) {
            outputDex.add(typeDeclaration.toClassDefItem());
        }

        try {
            return outputDex.toDex(null, false);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    // Generate a file name for the jar by taking a checksum of MethodIds and
    // parent class types.
    private String generateFileName() {
        int checksum = 1;

        Set<TypeId<?>> typesKeySet = types.keySet();
        Iterator<TypeId<?>> it = typesKeySet.iterator();
        int[] checksums = new int[typesKeySet.size()];
        int i = 0;

        while (it.hasNext()) {
            TypeId<?> typeId = it.next();
            TypeDeclaration decl = getTypeDeclaration(typeId);
            Set<MethodId> methodSet = decl.methods.keySet();
            if (decl.supertype != null) {
                checksums[i++] = 31 * decl.supertype.hashCode() + methodSet.hashCode();
            }
        }
        Arrays.sort(checksums);

        for (int sum : checksums) {
            checksum *= 31;
            checksum += sum;
        }

        return "Generated_" + checksum +".jar";
    }

    private ClassLoader generateClassLoader(File result, File dexCache, ClassLoader parent) {
        try {
            return (ClassLoader) Class.forName("dalvik.system.DexClassLoader")
                    .getConstructor(String.class, String.class, String.class, ClassLoader.class)
                    .newInstance(result.getPath(), dexCache.getAbsolutePath(), null, parent);
        } catch (ClassNotFoundException e) {
            throw new UnsupportedOperationException("load() requires a Dalvik VM", e);
        } catch (InvocationTargetException e) {
            throw new RuntimeException(e.getCause());
        } catch (InstantiationException e) {
            throw new AssertionError();
        } catch (NoSuchMethodException e) {
            throw new AssertionError();
        } catch (IllegalAccessException e) {
            throw new AssertionError();
        }
    }

    /**
     * Generates a dex file and loads its types into the current process.
     *
     * <h3>Picking a dex cache directory</h3>
     * The {@code dexCache} should be an application-private directory. If
     * you pass a world-writable directory like {@code /sdcard} a malicious app
     * could inject code into your process. Most applications should use this:
     * <pre>   {@code
     *
     *     File dexCache = getApplicationContext().getDir("dx", Context.MODE_PRIVATE);
     * }</pre>
     * If the {@code dexCache} is null, this method will consult the {@code
     * dexmaker.dexcache} system property. If that exists, it will be used for
     * the dex cache. If it doesn't exist, this method will attempt to guess
     * the application's private data directory as a last resort. If that fails,
     * this method will fail with an unchecked exception. You can avoid the
     * exception by either providing a non-null value or setting the system
     * property.
     *
     * @param parent the parent ClassLoader to be used when loading our
     *     generated types
     * @param dexCache the destination directory where generated and optimized
     *     dex files will be written. If null, this class will try to guess the
     *     application's private data dir.
     */
    public ClassLoader generateAndLoad(ClassLoader parent, File dexCache) throws IOException {
        if (dexCache == null) {
            String property = System.getProperty("dexmaker.dexcache");
            if (property != null) {
                dexCache = new File(property);
            } else {
                dexCache = new AppDataDirGuesser().guess();
                if (dexCache == null) {
                    throw new IllegalArgumentException("dexcache == null (and no default could be"
                            + " found; consider setting the 'dexmaker.dexcache' system property)");
                }
            }
        }

        File result = new File(dexCache, generateFileName());
        // Check that the file exists. If it does, return a DexClassLoader and skip all
        // the dex bytecode generation.
        if (result.exists()) {
            return generateClassLoader(result, dexCache, parent);
        }

        byte[] dex = generate();

        /*
         * This implementation currently dumps the dex to the filesystem. It
         * jars the emitted .dex for the benefit of Gingerbread and earlier
         * devices, which can't load .dex files directly.
         *
         * TODO: load the dex from memory where supported.
         */
        result.createNewFile();
        JarOutputStream jarOut = new JarOutputStream(new FileOutputStream(result));
        JarEntry entry = new JarEntry(DexFormat.DEX_IN_JAR_NAME);
        entry.setSize(dex.length);
        jarOut.putNextEntry(entry);
        jarOut.write(dex);
        jarOut.closeEntry();
        jarOut.close();
        return generateClassLoader(result, dexCache, parent);
    }

    private static class TypeDeclaration {
        private final TypeId<?> type;

        /** declared state */
        private boolean declared;
        private int flags;
        private TypeId<?> supertype;
        private String sourceFile;
        private TypeList interfaces;

        private final Map<FieldId, FieldDeclaration> fields
                = new LinkedHashMap<FieldId, FieldDeclaration>();
        private final Map<MethodId, MethodDeclaration> methods
                = new LinkedHashMap<MethodId, MethodDeclaration>();

        TypeDeclaration(TypeId<?> type) {
            this.type = type;
        }

        ClassDefItem toClassDefItem() {
            if (!declared) {
                throw new IllegalStateException("Undeclared type " + type + " declares members: "
                        + fields.keySet() + " " + methods.keySet());
            }

            DexOptions dexOptions = new DexOptions();
            dexOptions.targetApiLevel = DexFormat.API_NO_EXTENDED_OPCODES;

            CstType thisType = type.constant;

            ClassDefItem out = new ClassDefItem(thisType, flags, supertype.constant,
                    interfaces.ropTypes, new CstString(sourceFile));

            for (MethodDeclaration method : methods.values()) {
                EncodedMethod encoded = method.toEncodedMethod(dexOptions);
                if (method.isDirect()) {
                    out.addDirectMethod(encoded);
                } else {
                    out.addVirtualMethod(encoded);
                }
            }
            for (FieldDeclaration field : fields.values()) {
                EncodedField encoded = field.toEncodedField();
                if (field.isStatic()) {
                    out.addStaticField(encoded, Constants.getConstant(field.staticValue));
                } else {
                    out.addInstanceField(encoded);
                }
            }

            return out;
        }
    }

    static class FieldDeclaration {
        final FieldId<?, ?> fieldId;
        private final int accessFlags;
        private final Object staticValue;

        FieldDeclaration(FieldId<?, ?> fieldId, int accessFlags, Object staticValue) {
            if ((accessFlags & STATIC) == 0 && staticValue != null) {
                throw new IllegalArgumentException("instance fields may not have a value");
            }
            this.fieldId = fieldId;
            this.accessFlags = accessFlags;
            this.staticValue = staticValue;
        }

        EncodedField toEncodedField() {
            return new EncodedField(fieldId.constant, accessFlags);
        }

        public boolean isStatic() {
            return (accessFlags & STATIC) != 0;
        }
    }

    static class MethodDeclaration {
        final MethodId<?, ?> method;
        private final int flags;
        private final Code code;

        public MethodDeclaration(MethodId<?, ?> method, int flags) {
            this.method = method;
            this.flags = flags;
            this.code = new Code(this);
        }

        boolean isStatic() {
            return (flags & STATIC) != 0;
        }

        boolean isDirect() {
            return (flags & (STATIC | PRIVATE | ACC_CONSTRUCTOR)) != 0;
        }

        EncodedMethod toEncodedMethod(DexOptions dexOptions) {
            RopMethod ropMethod = new RopMethod(code.toBasicBlocks(), 0);
            LocalVariableInfo locals = null;
            DalvCode dalvCode = RopTranslator.translate(
                    ropMethod, PositionList.NONE, locals, code.paramSize(), dexOptions);
            return new EncodedMethod(method.constant, flags, dalvCode, StdTypeList.EMPTY);
        }
    }
}
