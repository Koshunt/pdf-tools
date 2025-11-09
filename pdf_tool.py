import sys
import os
import tempfile
from pathlib import Path
from PyQt5.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QPushButton, QFileDialog, QLabel, QMessageBox, QListWidget, QListWidgetItem,
    QInputDialog, QAction, QGraphicsView, QGraphicsScene, QSplitter, QFrame,
    QGraphicsProxyWidget
)
from PyQt5.QtGui import QPixmap, QImage, QPainter, QKeySequence, QIcon
from PyQt5.QtCore import Qt, QRectF, QSize, QUrl, QEvent
from pypdf import PdfWriter, PdfReader
from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import letter
import io
import shutil

# ======================
# 自动定位同目录下的 poppler
# ======================
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
POPPLER_PATH = os.path.join(SCRIPT_DIR, "poppler", "Library", "bin")

if not os.path.exists(os.path.join(POPPLER_PATH, "pdftoppm.exe")):
    POPPLER_PATH = None

# ======================
# 尝试导入 pdf2image
# ======================
try:
    from pdf2image import convert_from_path
    PDF_PREVIEW_AVAILABLE = True
except ImportError:
    PDF_PREVIEW_AVAILABLE = False

try:
    from PIL.ImageQt import ImageQt
except ImportError:
    def ImageQt(img):
        if img.mode != "RGBA":
            img = img.convert("RGBA")
        data = img.tobytes("raw", "RGBA")
        qim = QImage(data, img.size[0], img.size[1], QImage.Format_RGBA8888)
        return qim


def create_blank_page():
    packet = io.BytesIO()
    can = canvas.Canvas(packet, pagesize=letter)
    can.setFont("Helvetica", 1)
    can.drawString(0, 0, " ")
    can.showPage()
    can.save()
    packet.seek(0)
    return PdfReader(packet)


def parse_page_ranges(range_str, total_pages):
    if not range_str.strip():
        return []
    pages = set()
    parts = range_str.replace(" ", "").split(",")
    for part in parts:
        if "-" in part:
            try:
                start, end = map(int, part.split("-"))
                if 1 <= start <= end <= total_pages:
                    pages.update(range(start, end + 1))
                else:
                    raise ValueError
            except:
                raise ValueError(f"无效范围: {part}")
        else:
            try:
                p = int(part)
                if 1 <= p <= total_pages:
                    pages.add(p)
                else:
                    raise ValueError
            except:
                raise ValueError(f"无效页码: {part}")
    return sorted(pages)


class PDFPreviewView(QGraphicsView):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setRenderHint(QPainter.Antialiasing)
        self.setRenderHint(QPainter.SmoothPixmapTransform)
        self.setBackgroundBrush(Qt.lightGray)
        self.setDragMode(QGraphicsView.ScrollHandDrag)
        self.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
        self.setResizeAnchor(QGraphicsView.AnchorUnderMouse)

    def wheelEvent(self, event):
        if event.modifiers() == Qt.ControlModifier:
            # Ctrl + 滚轮：缩放
            zoom_factor = 1.15 if event.angleDelta().y() > 0 else 1 / 1.15
            self.scale(zoom_factor, zoom_factor)
            event.accept()
        else:
            # 默认：滚轮翻页
            delta = event.angleDelta().y()
            main_window = self.window()
            if hasattr(main_window, 'next_page') and hasattr(main_window, 'prev_page'):
                if delta < 0:
                    main_window.next_page()
                else:
                    main_window.prev_page()
            event.accept()


class PageListWidget(QListWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setDragEnabled(False)
        self.setAcceptDrops(False)
        self.setDragDropMode(QListWidget.NoDragDrop)
        self.setDefaultDropAction(Qt.IgnoreAction)
        self.setSelectionMode(QListWidget.SingleSelection)
        self.setSpacing(6)
        self._icon_width = -1
        self.setIconSize(QSize(120, 168))
        self.setStyleSheet("""
            QListWidget::item:selected {
                border: 2px solid #0078d7;
                border-radius: 4px;
            }
        """)

    def update_icon_size(self, width=None):
        if width is None:
            if self._icon_width == -1:
                w = max(60, self.width() - 30)
            else:
                w = max(60, min(300, self._icon_width))
        else:
            w = max(60, min(300, width))
        h = int(w * 1.4)
        self.setIconSize(QSize(w, h))

    def resizeEvent(self, event):
        super().resizeEvent(event)
        if self._icon_width == -1:
            self.update_icon_size()

    def wheelEvent(self, event):
        if event.modifiers() == Qt.ControlModifier:
            delta = event.angleDelta().y()
            self._icon_width = self.iconSize().width() + (10 if delta > 0 else -10)
            self._icon_width = max(60, min(300, self._icon_width))
            self.update_icon_size()
            event.accept()
        else:
            super().wheelEvent(event)


class PDFToolWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("PDF 工具箱")
        self.setGeometry(100, 100, 1200, 800)
        self.current_pdf_path = None
        self.page_images = []
        self.current_page_index = 0
        self.reader = None
        self.thumbnail_panel_visible = True
        self.undo_stack = []
        self.MAX_UNDO = 5
        self.open_button_proxy = None

        # 添加用于跟踪单击操作的变量
        self.last_clicked_operation = None
        self.last_operation_params = None

        self.setAcceptDrops(True)
        self.init_ui()
        self.create_actions()
        self.show_open_button()

        # 安装事件过滤器用于双击
        self.move_up_btn.installEventFilter(self)
        self.move_down_btn.installEventFilter(self)
        self.delete_current_btn.installEventFilter(self)
        self.add_blank_btn.installEventFilter(self)

    def eventFilter(self, obj, event):
        if event.type() == QEvent.MouseButtonDblClick:
            if obj == self.move_up_btn:
                self.handle_double_click(self.move_current_up_multi, self.move_current_up)
                return True
            elif obj == self.move_down_btn:
                self.handle_double_click(self.move_current_down_multi, self.move_current_down)
                return True
            elif obj == self.delete_current_btn:
                self.handle_double_click(self.delete_current_pages_multi, self.delete_current_page)
                return True
            elif obj == self.add_blank_btn:
                self.handle_double_click(self.add_blank_pages_multi, self.add_blank_after_current)
                return True
        return super().eventFilter(obj, event)

    def handle_double_click(self, double_click_func, single_click_func):
        """处理双击事件：先撤销单击效果，再执行双击功能"""
        # 如果之前有单击操作，则撤销它
        if self.last_clicked_operation == single_click_func.__name__:
            self.undo_last_operation()
        
        # 重置最后操作记录
        self.last_clicked_operation = None
        self.last_operation_params = None
        
        # 执行双击操作
        double_click_func()

    def undo_last_operation(self):
        """撤销最后的操作"""
        if self.undo_stack:
            prev_path, prev_index = self.undo_stack.pop()
            try:
                self.load_pdf(prev_path, is_undo=True)
                self.current_page_index = prev_index
                self.update_preview()
            except Exception as e:
                QMessageBox.critical(self, "撤销失败", f"无法恢复上一状态:\n{str(e)}")
            finally:
                if hasattr(self, '_last_temp') and os.path.exists(self._last_temp):
                    try:
                        os.remove(self._last_temp)
                    except:
                        pass
                self._last_temp = prev_path
            self.undo_btn.setEnabled(len(self.undo_stack) > 0)

    def init_ui(self):
        central = QWidget()
        main_layout = QVBoxLayout()
        central.setLayout(main_layout)
        self.setCentralWidget(central)

        self.splitter = QSplitter(Qt.Horizontal)
        main_layout.addWidget(self.splitter)

        self.thumbnail_frame = QFrame()
        thumbnail_layout = QVBoxLayout(self.thumbnail_frame)
        thumbnail_layout.setContentsMargins(0, 0, 0, 0)

        self.thumbnail_list = PageListWidget()
        self.thumbnail_list.itemClicked.connect(self.on_thumbnail_click)
        thumbnail_layout.addWidget(self.thumbnail_list)

        self.hide_btn = QPushButton("◀")
        self.hide_btn.setFixedWidth(20)
        self.hide_btn.clicked.connect(self.toggle_thumbnail_panel)
        thumbnail_layout.addWidget(self.hide_btn, alignment=Qt.AlignRight)

        right_widget = QWidget()
        right_layout = QVBoxLayout(right_widget)
        right_layout.setContentsMargins(0, 0, 0, 0)

        self.scene = QGraphicsScene()
        self.view = PDFPreviewView()
        self.view.setScene(self.scene)
        right_layout.addWidget(self.view, 1)

        control_layout = QHBoxLayout()
        self.page_label = QLabel("页面: - / -")
        self.prev_btn = QPushButton("◀ 上一页")
        self.next_btn = QPushButton("下一页 ▶")
        self.move_up_btn = QPushButton("↑ 上移页面")
        self.move_down_btn = QPushButton("↓ 下移页面")
        self.delete_current_btn = QPushButton("删除当前页")
        self.add_blank_btn = QPushButton("插入空白页")
        self.split_by_range_btn = QPushButton("按范围分割...")
        self.add_pdf_btn = QPushButton("添加 PDF")
        self.undo_btn = QPushButton("撤销")
        self.save_btn = QPushButton("保存 PDF")

        # 为每个按钮连接单击事件，并记录操作类型
        self.prev_btn.clicked.connect(self.prev_page)
        self.next_btn.clicked.connect(self.next_page)
        self.move_up_btn.clicked.connect(self.move_current_up_with_tracking)
        self.move_down_btn.clicked.connect(self.move_current_down_with_tracking)
        self.delete_current_btn.clicked.connect(self.delete_current_page_with_tracking)
        self.add_blank_btn.clicked.connect(self.add_blank_after_current_with_tracking)
        self.split_by_range_btn.clicked.connect(self.split_by_range)
        self.add_pdf_btn.clicked.connect(self.add_pdf)
        self.undo_btn.clicked.connect(self.undo)
        self.save_btn.clicked.connect(self.save_pdf)

        buttons = [
            self.page_label,
            self.prev_btn, self.next_btn,
            self.move_up_btn, self.move_down_btn,
            self.delete_current_btn, self.add_blank_btn,
            self.split_by_range_btn, self.add_pdf_btn,
            self.undo_btn, self.save_btn
        ]
        for btn in buttons:
            if isinstance(btn, QPushButton):
                btn.setStyleSheet("padding: 4px 8px;")
        for btn in buttons:
            control_layout.addWidget(btn)

        right_layout.addLayout(control_layout)

        self.show_btn = QPushButton("▶")
        self.show_btn.setFixedWidth(20)
        self.show_btn.clicked.connect(self.toggle_thumbnail_panel)
        self.show_btn.hide()
        right_layout.addWidget(self.show_btn, alignment=Qt.AlignLeft)

        self.splitter.addWidget(self.thumbnail_frame)
        self.splitter.addWidget(right_widget)
        self.splitter.setSizes([250, 950])

        self.update_add_pdf_button_state()

    def update_add_pdf_button_state(self):
        enabled = self.current_pdf_path is not None
        self.add_pdf_btn.setEnabled(enabled)

    def show_open_button(self):
        self.scene.clear()
        open_btn = QPushButton("📁 打开 PDF 文件")
        open_btn.setFixedSize(220, 60)
        open_btn.setStyleSheet("""
            QPushButton {
                font-size: 16px;
                font-weight: bold;
                color: white;
                background-color: transparent;
                border: 2px dashed #aaa;
                border-radius: 10px;
            }
            QPushButton:hover {
                background-color: rgba(255, 0, 0, 30);
            }
        """)
        open_btn.clicked.connect(self.open_pdfs)
        proxy = self.scene.addWidget(open_btn)
        self.open_button_proxy = proxy
        self.update_open_button_position()

    def update_open_button_position(self):
        if self.open_button_proxy:
            view_w = self.view.viewport().width()
            view_h = self.view.viewport().height()
            btn_w = self.open_button_proxy.widget().width()
            btn_h = self.open_button_proxy.widget().height()
            x = (view_w - btn_w) / 2
            y = (view_h - btn_h) / 2
            self.open_button_proxy.setPos(x, y)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self.update_open_button_position()

    def hide_open_button(self):
        if self.open_button_proxy:
            self.scene.removeItem(self.open_button_proxy)
            self.open_button_proxy = None

    def toggle_thumbnail_panel(self):
        self.thumbnail_panel_visible = not self.thumbnail_panel_visible
        if self.thumbnail_panel_visible:
            self.thumbnail_frame.show()
            self.show_btn.hide()
            self.splitter.setSizes([250, self.width() - 250])
        else:
            self.thumbnail_frame.hide()
            self.show_btn.show()

    def create_actions(self):
        menubar = self.menuBar()
        file_menu = menubar.addMenu("文件")
        open_action = QAction("打开 PDF...", self)
        open_action.setShortcut(QKeySequence.Open)
        open_action.triggered.connect(self.open_pdfs)
        file_menu.addAction(open_action)

        full_screen_action = QAction("全屏预览 (F11)", self)
        full_screen_action.setShortcut("F11")
        full_screen_action.triggered.connect(self.toggle_fullscreen)
        file_menu.addAction(full_screen_action)

        exit_action = QAction("退出", self)
        exit_action.triggered.connect(self.close)
        file_menu.addAction(exit_action)

    def toggle_fullscreen(self):
        if self.isFullScreen():
            self.showNormal()
        else:
            self.showFullScreen()

    def _push_undo_state(self):
        if not self.current_pdf_path:
            return
        fd, temp_path = tempfile.mkstemp(suffix=".pdf")
        os.close(fd)
        shutil.copy(self.current_pdf_path, temp_path)
        self.undo_stack.append((temp_path, self.current_page_index))
        if len(self.undo_stack) > self.MAX_UNDO:
            old_path, _ = self.undo_stack.pop(0)
            try:
                os.remove(old_path)
            except:
                pass
        self.undo_btn.setEnabled(True)

    def undo(self):
        if not self.undo_stack:
            return
        prev_path, prev_index = self.undo_stack.pop()
        try:
            self.load_pdf(prev_path, is_undo=True)
            self.current_page_index = prev_index
            self.update_preview()
        except Exception as e:
            QMessageBox.critical(self, "撤销失败", f"无法恢复上一状态:\n{str(e)}")
        finally:
            if hasattr(self, '_last_temp') and os.path.exists(self._last_temp):
                try:
                    os.remove(self._last_temp)
                except:
                    pass
            self._last_temp = prev_path
        self.undo_btn.setEnabled(len(self.undo_stack) > 0)

    def open_pdfs(self):
        files, _ = QFileDialog.getOpenFileNames(self, "选择 PDF 文件", "", "PDF Files (*.pdf)")
        if not files:
            return
        self.process_pdf_files(files)

    def process_pdf_files(self, files):
        if len(files) == 1:
            self.load_pdf(files[0])
        else:
            fd, merged_path = tempfile.mkstemp(suffix="_merged.pdf")
            os.close(fd)
            writer = PdfWriter()
            for f in files:
                reader = PdfReader(f)
                for page in reader.pages:
                    writer.add_page(page)
            with open(merged_path, "wb") as out:
                writer.write(out)
            self.load_pdf(merged_path, is_merged=True)
            self._push_undo_state()
        self.update_add_pdf_button_state()

    def add_pdf(self):
        if not self.current_pdf_path:
            return
        files, _ = QFileDialog.getOpenFileNames(self, "选择要添加的 PDF 文件", "", "PDF Files (*.pdf)")
        if not files:
            return

        self._push_undo_state()

        writer = PdfWriter()
        current_reader = PdfReader(self.current_pdf_path)
        for page in current_reader.pages:
            writer.add_page(page)

        for f in files:
            new_reader = PdfReader(f)
            for page in new_reader.pages:
                writer.add_page(page)

        fd, temp_path = tempfile.mkstemp(suffix="_appended.pdf")
        os.close(fd)
        with open(temp_path, "wb") as out:
            writer.write(out)

        self.load_pdf(temp_path)
        self.update_add_pdf_button_state()

    def load_pdf(self, pdf_path, is_merged=False, is_undo=False):
        try:
            self.reader = PdfReader(pdf_path)
            total = len(self.reader.pages)
            if total == 0:
                QMessageBox.warning(self, "错误", "PDF 无页面！")
                return

            if not PDF_PREVIEW_AVAILABLE:
                raise Exception("请安装 pdf2image")

            images = convert_from_path(
                pdf_path,
                dpi=100,
                poppler_path=POPPLER_PATH,
                thread_count=1
            )
            self.page_images = images
            self.current_pdf_path = pdf_path

            self.thumbnail_list.clear()
            for i, img in enumerate(images):
                qimage = ImageQt(img)
                pixmap = QPixmap.fromImage(qimage)
                item = QListWidgetItem()
                item.setIcon(QIcon(pixmap))
                item.setData(Qt.UserRole, i)
                self.thumbnail_list.addItem(item)

            self.current_page_index = 0 if not is_undo else self.current_page_index
            self.update_preview()
            self.update_add_pdf_button_state()
        except Exception as e:
            QMessageBox.critical(self, "加载失败", f"无法加载 PDF:\n{str(e)}")

    def update_preview(self):
        self.hide_open_button()
        self.scene.clear()
        total = len(self.page_images)
        if total == 0:
            self.page_label.setText("页面: - / -")
            return

        idx = max(0, min(self.current_page_index, total - 1))
        img = self.page_images[idx]
        qimage = ImageQt(img)
        pixmap = QPixmap.fromImage(qimage)
        self.scene.addPixmap(pixmap)
        self.scene.setSceneRect(QRectF(pixmap.rect()))
        self.view.resetTransform()
        self.view.fitInView(self.scene.sceneRect(), Qt.KeepAspectRatio)

        self.page_label.setText(f"页面: {idx + 1} / {total}")
        self.thumbnail_list.blockSignals(True)
        self.thumbnail_list.setCurrentRow(idx)
        self.thumbnail_list.blockSignals(False)

    def on_thumbnail_click(self, item):
        self.current_page_index = item.data(Qt.UserRole)
        self.update_preview()

    def move_page(self, from_index, to_index):
        if from_index == to_index:
            return
        self._push_undo_state()
        pages = list(self.reader.pages)
        page_to_move = pages.pop(from_index)
        pages.insert(to_index, page_to_move)

        fd, temp_path = tempfile.mkstemp(suffix=".pdf")
        os.close(fd)
        writer = PdfWriter()
        for page in pages:
            writer.add_page(page)
        with open(temp_path, "wb") as f:
            writer.write(f)

        if self.current_page_index == from_index:
            new_current = to_index
        elif from_index < self.current_page_index <= to_index:
            new_current = self.current_page_index - 1
        elif to_index <= self.current_page_index < from_index:
            new_current = self.current_page_index + 1
        else:
            new_current = self.current_page_index

        self.load_pdf(temp_path)
        self.current_page_index = new_current
        self.update_preview()

    def move_current_up_with_tracking(self):
        self.last_clicked_operation = "move_current_up"
        self.move_current_up()

    def move_current_up(self):
        if self.current_page_index > 0:
            self.move_page(self.current_page_index, self.current_page_index - 1)

    def move_current_down_with_tracking(self):
        self.last_clicked_operation = "move_current_down"
        self.move_current_down()

    def move_current_down(self):
        if self.current_page_index < len(self.page_images) - 1:
            self.move_page(self.current_page_index, self.current_page_index + 1)

    def prev_page(self):
        if self.current_page_index > 0:
            self.current_page_index -= 1
            self.update_preview()

    def next_page(self):
        if self.current_page_index < len(self.page_images) - 1:
            self.current_page_index += 1
            self.update_preview()

    def delete_current_page_with_tracking(self):
        self.last_clicked_operation = "delete_current_page"
        self.delete_current_page()

    def delete_current_page(self):
        if not self.reader or len(self.page_images) <= 1:
            return
        self._push_undo_state()
        fd, temp_path = tempfile.mkstemp(suffix=".pdf")
        os.close(fd)
        writer = PdfWriter()
        for i, page in enumerate(self.reader.pages):
            if i != self.current_page_index:
                writer.add_page(page)
        with open(temp_path, "wb") as f:
            writer.write(f)
        self.load_pdf(temp_path)

    def add_blank_after_current_with_tracking(self):
        self.last_clicked_operation = "add_blank_after_current"
        self.add_blank_after_current()

    def add_blank_after_current(self):
        if not self.reader:
            return
        self._push_undo_state()
        pos = self.current_page_index + 1
        fd, temp_path = tempfile.mkstemp(suffix=".pdf")
        os.close(fd)
        blank = create_blank_page().pages[0]
        writer = PdfWriter()
        pages = list(self.reader.pages)
        pages.insert(pos, blank)
        for page in pages:
            writer.add_page(page)
        with open(temp_path, "wb") as f:
            writer.write(f)
        self.load_pdf(temp_path)
        self.current_page_index = pos
        self.update_preview()

    def split_by_range(self):
        if not self.reader:
            return
        total = len(self.reader.pages)
        text, ok = QInputDialog.getText(
            self, "按范围分割",
            f"请输入页面范围（例如：1-3,5,7-9），共 {total} 页："
        )
        if not ok or not text.strip():
            return
        try:
            selected_pages = parse_page_ranges(text, total)
            if not selected_pages:
                QMessageBox.warning(self, "无效输入", "未选择任何有效页面！")
                return
        except ValueError as e:
            QMessageBox.critical(self, "格式错误", f"页面范围格式错误：\n{e}")
            return

        self._push_undo_state()
        fd, temp_path = tempfile.mkstemp(suffix=".pdf")
        os.close(fd)
        writer = PdfWriter()
        for p in selected_pages:
            writer.add_page(self.reader.pages[p - 1])
        with open(temp_path, "wb") as f:
            writer.write(f)
        self.load_pdf(temp_path)

    def save_pdf(self):
        if not self.current_pdf_path:
            return
        save_path, _ = QFileDialog.getSaveFileName(
            self, "保存 PDF 文件", "output.pdf", "PDF Files (*.pdf)"
        )
        if save_path:
            if not save_path.endswith(".pdf"):
                save_path += ".pdf"
            shutil.copy(self.current_pdf_path, save_path)
            QMessageBox.information(self, "成功", f"文件已保存至：\n{save_path}")

    def dragEnterEvent(self, event):
        mime = event.mimeData()
        if mime.hasUrls():
            urls = mime.urls()
            if all(url.toLocalFile().lower().endswith('.pdf') for url in urls):
                event.acceptProposedAction()
                return
        event.ignore()

    def dropEvent(self, event):
        mime = event.mimeData()
        if mime.hasUrls():
            files = [url.toLocalFile() for url in mime.urls() if url.toLocalFile().lower().endswith('.pdf')]
            if files:
                self.process_pdf_files(files)
                event.acceptProposedAction()
                return
        event.ignore()

    # ========== 新增多页操作 ==========
    def move_current_up_multi(self):
        if self.current_page_index <= 0:
            return
        max_move = self.current_page_index
        n, ok = QInputDialog.getInt(self, "上移页面", f"向上移动多少页？(1-{max_move})", 1, 1, max_move)
        if ok and n > 0:
            for _ in range(n):
                if self.current_page_index <= 0:
                    break
                self.move_page(self.current_page_index, self.current_page_index - 1)

    def move_current_down_multi(self):
        total = len(self.page_images) if self.page_images else 0
        if self.current_page_index >= total - 1:
            return
        max_move = total - 1 - self.current_page_index
        n, ok = QInputDialog.getInt(self, "下移页面", f"向下移动多少页？(1-{max_move})", 1, 1, max_move)
        if ok and n > 0:
            for _ in range(n):
                if self.current_page_index >= total - 1:
                    break
                self.move_page(self.current_page_index, self.current_page_index + 1)

    def delete_current_pages_multi(self):
        total = len(self.page_images) if self.page_images else 0
        if total <= 1:
            return
        max_del = total - self.current_page_index
        n, ok = QInputDialog.getInt(self, "删除页面", f"从当前页开始删除多少页？(1-{max_del})", 1, 1, max_del)
        if ok and n > 0:
            self._push_undo_state()
            fd, temp_path = tempfile.mkstemp(suffix=".pdf")
            os.close(fd)
            writer = PdfWriter()
            for i, page in enumerate(self.reader.pages):
                if i < self.current_page_index or i >= self.current_page_index + n:
                    writer.add_page(page)
            with open(temp_path, "wb") as f:
                writer.write(f)
            self.load_pdf(temp_path)

    def add_blank_pages_multi(self):
        if not self.reader:
            return
        n, ok = QInputDialog.getInt(self, "插入空白页", "插入多少空白页？", 1, 1, 50)
        if ok and n > 0:
            self._push_undo_state()
            pos = self.current_page_index + 1
            fd, temp_path = tempfile.mkstemp(suffix=".pdf")
            os.close(fd)
            blank_page = create_blank_page().pages[0]
            writer = PdfWriter()
            pages = list(self.reader.pages)
            for _ in range(n):
                pages.insert(pos, blank_page)
                pos += 1
            for page in pages:
                writer.add_page(page)
            with open(temp_path, "wb") as f:
                writer.write(f)
            self.load_pdf(temp_path)
            self.current_page_index = pos - 1
            self.update_preview()


if __name__ == "__main__":
    app = QApplication(sys.argv)
    window = PDFToolWindow()
    window.show()
    sys.exit(app.exec_())