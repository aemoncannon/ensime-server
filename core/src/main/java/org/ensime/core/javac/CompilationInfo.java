package org.ensime.core.javac;

import com.sun.source.tree.*;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.util.SourcePositions;
import com.sun.source.util.TreePath;
import com.sun.source.util.TreePathScanner;
import com.sun.source.util.TreeScanner;
import com.sun.tools.javac.api.JavacScope;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Enter;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.Resolve;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.util.Context;
import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.lang.model.SourceVersion;
import javax.lang.model.element.*;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import javax.lang.model.type.UnionType;
import javax.lang.model.util.Types;
import org.netbeans.api.java.lexer.JavaTokenId;
import org.netbeans.api.java.source.JavaSource.Phase;
import org.netbeans.api.lexer.TokenSequence;
import org.netbeans.modules.java.source.builder.CommentHandlerService;
import org.netbeans.modules.java.source.builder.CommentSetImpl;
import org.netbeans.modules.java.source.pretty.ImportAnalysis2;
import org.netbeans.modules.java.source.transform.ImmutableTreeTranslator;
import org.netbeans.api.lexer.TokenHierarchy;
import java.util.HashSet;
import java.io.Reader;
import java.io.IOException;
import com.sun.source.util.Trees;
import javax.lang.model.util.Elements;
import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.util.JavacTask;
import org.netbeans.api.lexer.InputAttributes;

public final class CompilationInfo {
    private final JavacTask javacTask;
    private final Trees trees;
    private final TokenHierarchy<Reader> tokenHierarchy;
    private final CompilationUnitTree compilationUnit;

    public CompilationInfo(final JavacTask javacTask,
                           final CompilationUnitTree compilationUnit) throws IOException {
        boolean ignoreEncodingErrors = true;
        this.javacTask = javacTask;
        this.trees = Trees.instance(javacTask);
        this.tokenHierarchy =
            TokenHierarchy.create(compilationUnit.getSourceFile().openReader(ignoreEncodingErrors),
                                  JavaTokenId.language(),
                                  new HashSet<JavaTokenId>(),
                                  new InputAttributes());
        this.compilationUnit = compilationUnit;
    }

    public CompilationInfo(final JavacTask javacTask,
                           final Element element) throws IOException {
        this(javacTask, (CompilationUnitTree)(Trees.instance(javacTask).getTree(element.getEnclosingElement())));
    }

    public JavacTask getJavacTask() { return javacTask; }
    public Trees getTrees() { return trees; }
    public Types getTypes() { return javacTask.getTypes(); }
    public Elements getElements() { return javacTask.getElements(); }
    public TokenHierarchy<Reader> getTokenHierarchy() { return tokenHierarchy; }
    public CompilationUnitTree getCompilationUnit() { return compilationUnit; }
}
